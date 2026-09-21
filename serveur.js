'use strict';
/* ===================================================================
   CASINO MESSINA — serveur de jeu
   -------------------------------------------------------------------
   Aucune bibliotheque a installer : uniquement Node.
   Le serveur tient les cartes, les tours et le chronometre.
   Regle absolue : chaque phase a une duree maximum. Quand le temps
   est ecoule, la partie avance, que les joueurs aient repondu ou non.
   Personne ne peut bloquer personne.
   =================================================================== */

const http   = require('http');
const fs     = require('fs');
const path   = require('path');
const crypto = require('crypto');

const PORT    = process.env.PORT || 3000;
const DOSSIER = __dirname;

/* ---------- durees, en millisecondes ---------- */
const DUREE_MISE      = 10000;  // temps pour miser
const DUREE_TOUR      = 10000;  // temps pour jouer son tour
const DUREE_RESULTAT  = 5200;   // affichage du resultat avant la manche suivante
const DELAI_CARTE     = 430;    // entre deux cartes distribuees
const DELAI_BANQUE    = 760;    // entre deux cartes de la banque
const DELAI_BOT       = 900;    // temps de reflexion d'un bot
const ABSENCE_MAX     = 15000;  // sans nouvelles, un joueur perd sa place
const SOLDE_DEPART    = 22;

/* ---------- le penalty ----------
   L'echelle des gains : un but = on monte d'un cran.
   Le joueur peut encaisser quand il veut ; s'il rate, il perd sa mise.
   Le tirage se fait ICI, sur le serveur : impossible de tricher
   en bidouillant la page.                                          */
const ECHELLE_PENALTY  = [2, 4, 8, 16, 32, 64, 100];
const CHANCE_BUT       = 4700;   // sur 10000, soit 47 % de buts (53 % d'arrets)
const MISE_MINI_PENALTY = 0.10;
const ZONES_PENALTY    = 15;     // la cage est decoupee en 5 x 3
const DEFAITES_SECRET  = 2;      // apres deux echecs, la tete du gardien compte

/* ---------- le jeu du periph ----------
   Douze portes de la Porte Dauphine a Saint-Denis. A chaque porte
   franchie la somme monte ; au bout du parcours elle vaut cinquante
   fois la mise. Le joueur peut encaisser a chaque porte.
   La course se joue dans la page, mais l'argent se compte ICI :
   la mise part au depart, le gain n'est verse que par ce fichier, et
   le serveur refuse une porte annoncee trop tot pour la distance.   */
const ECHELLE_PERIPH   = [1.4, 2, 2.7, 3.8, 5.3, 7.5, 10.4, 14.6, 20.4, 28.5, 39.8, 50];
const LONGUEURS_PERIPH = [900, 300, 300, 550, 650, 650, 800, 800, 850, 800, 650, 550];
const NOMS_PERIPH      = ['Porte Maillot','Porte des Ternes','Porte de Villiers',
                          'Porte de Champerret','Porte d\u2019Asni\u00e8res','Porte de Clichy',
                          'Porte de Saint-Ouen','Porte de Clignancourt','Porte de la Chapelle',
                          'Porte d\u2019Aubervilliers','Porte de la Villette','Saint-Denis'];
const MISE_MINI_PERIPH = 0.10;
const MISE_MAXI_PERIPH = 100;
const VITESSE_MAX_PERIPH = 150 / 3.6;   // metres par seconde
const MARGE_TEMPS      = 0.80;          // on tolere un peu de retard d'horloge

/* la voiture de la boutique : plus rapide, avec des vrais freins */
const PRIX_VOITURE_PREMIUM     = 1200;
const VOITURE_PREMIUM_INDICE   = 4;
const VITESSE_MAX_PERIPH_PREMIUM = 300 / 3.6;   // metres par seconde

function distancePeriph(palier) {
  let s = 0;
  for (let i = 0; i < palier && i < LONGUEURS_PERIPH.length; i++) s += LONGUEURS_PERIPH[i];
  return s;
}
function bornerVoitureNormale(v) {
  v = Number(v) | 0;
  return (v >= 0 && v < VOITURE_PREMIUM_INDICE) ? v : 0;
}

/* ===================================================================
   CARTES
   =================================================================== */
const ENSEIGNES = [
  { s: '♠', r: false }, { s: '♥', r: true },
  { s: '♦', r: true  }, { s: '♣', r: false }
];
const HAUTEURS = ['A', '2', '3', '4', '5', '6', '7', '8', '9', '10', 'V', 'D', 'R'];

function neufSabot() {
  const sabot = [];
  for (let p = 0; p < 6; p++)
    for (const e of ENSEIGNES)
      for (const h of HAUTEURS)
        sabot.push({ h, s: e.s, r: e.r });
  for (let i = sabot.length - 1; i > 0; i--) {
    const j = crypto.randomInt(i + 1);
    const t = sabot[i]; sabot[i] = sabot[j]; sabot[j] = t;
  }
  return sabot;
}
function valeurCarte(c) {
  if (c.h === 'A') return 11;
  if (c.h === 'V' || c.h === 'D' || c.h === 'R') return 10;
  return parseInt(c.h, 10);
}
function compter(main) {
  let total = 0, as = 0;
  for (const c of main) { total += valeurCarte(c); if (c.h === 'A') as++; }
  while (total > 21 && as > 0) { total -= 10; as--; }
  return total;
}
function estBlackjack(main) { return main.length === 2 && compter(main) === 21; }
function sous(n) { return Math.round(n * 100) / 100; }

/* ===================================================================
   LE CARNET DES JOUEURS
   -------------------------------------------------------------------
   Les comptes sont rangés dans une base Upstash, jointe par simple
   requête web, pour qu'ils survivent quand l'hébergeur éteint et
   rallume le site. Aucune bibliothèque à installer.
   Si aucune base n'est configurée, le site fonctionne quand même :
   les comptes sont simplement gardés en mémoire jusqu'au prochain
   redémarrage. Le jeu n'est jamais bloqué par la base.
   =================================================================== */
const Carnet = {
  url: null,
  token: null,
  pret: false,
  memoire: new Map(),        // repli, et copie de travail

  async demarrer() {
    const url   = String(process.env.UPSTASH_REDIS_REST_URL   || '').replace(/\/+$/, '');
    const token = String(process.env.UPSTASH_REDIS_REST_TOKEN || '');

    if (!url || !token) {
      console.log('Carnet : aucune base configurée.');
      console.log('Le jeu tourne, mais les comptes seront perdus au redémarrage.');
      return;
    }
    this.url = url;
    this.token = token;
    try {
      const r = await this.commande(['PING']);
      if (r && r.result) {
        this.pret = true;
        console.log('Carnet : base connectée, les comptes sont conservés.');
      } else {
        console.log('Carnet : la base a répondu quelque chose d’inattendu.');
      }
    } catch (e) {
      console.log('Carnet : connexion à la base impossible (' + e.message + ').');
      console.log('Le jeu tourne quand même, mais les comptes ne seront pas conservés.');
    }
  },

  async commande(args) {
    const reponse = await fetch(this.url, {
      method: 'POST',
      headers: {
        'Authorization': 'Bearer ' + this.token,
        'Content-Type': 'application/json'
      },
      body: JSON.stringify(args),
      signal: AbortSignal.timeout(8000)
    });
    if (!reponse.ok) throw new Error('HTTP ' + reponse.status);
    return await reponse.json();
  },

  async lire(pseudoBas) {
    if (!this.pret) return this.memoire.get(pseudoBas) || null;
    try {
      const r = await this.commande(['GET', 'joueur:' + pseudoBas]);
      if (!r || r.result === null || r.result === undefined) return null;
      const fiche = JSON.parse(r.result);
      this.memoire.set(pseudoBas, fiche);        // on garde une copie sous la main
      return fiche;
    } catch (e) {
      console.log('Carnet : lecture impossible (' + e.message + ')');
      return this.memoire.get(pseudoBas) || null;
    }
  },

  async creer(fiche) {
    fiche.creeLe = new Date().toISOString();
    this.memoire.set(fiche.pseudoBas, fiche);
    if (!this.pret) return true;
    try {
      // SETNX n'écrit que si le pseudo est encore libre
      const r = await this.commande(['SETNX', 'joueur:' + fiche.pseudoBas, JSON.stringify(fiche)]);
      return !!(r && Number(r.result) === 1);
    } catch (e) {
      console.log('Carnet : création impossible (' + e.message + ')');
      return true;                                // on laisse quand même jouer
    }
  },

  // Enregistre l'avancement. N'interrompt jamais la partie : si la base
  // ne répond pas, on note l'échec et le jeu continue.
  enregistrer(compte) {
    const ancienne = this.memoire.get(compte.pseudoBas) || {};
    const fiche = Object.assign({}, ancienne, {
      pseudoBas: compte.pseudoBas,
      pseudo:    compte.pseudo,
      solde:     compte.solde,
      mains:     compte.mains,
      gagnees:   compte.gagnees,
      perdues:   compte.perdues,
      poissons:  compte.poissons,
      penaltys:  compte.penaltys,
      buts:      compte.buts,
      defaitesPenalty: compte.defaitesPenalty | 0,
      periphs:   compte.periphs | 0,
      portes:    compte.portes  | 0,
      voiturePremium: !!compte.voiturePremium,
      perso:     compte.perso || ancienne.perso || null,
      vuLe:      new Date().toISOString()
    });
    this.memoire.set(compte.pseudoBas, fiche);

    if (!this.pret) return;
    this.commande(['SET', 'joueur:' + compte.pseudoBas, JSON.stringify(fiche)])
      .catch(e => console.log('Carnet : enregistrement impossible (' + e.message + ')'));
  }
};

/* ---------- mots de passe : jamais stockés en clair ---------- */
function empreinte(motDePasse, sel) {
  return new Promise((resolve, reject) => {
    crypto.scrypt(motDePasse, sel, 32, (err, cle) => err ? reject(err) : resolve(cle.toString('hex')));
  });
}
async function chiffrer(motDePasse) {
  const sel = crypto.randomBytes(16).toString('hex');
  return sel + ':' + await empreinte(motDePasse, sel);
}
async function motDePasseJuste(motDePasse, stocke) {
  const bouts = String(stocke || '').split(':');
  if (bouts.length !== 2) return false;
  try {
    const calcule = Buffer.from(await empreinte(motDePasse, bouts[0]), 'hex');
    const attendu = Buffer.from(bouts[1], 'hex');
    return calcule.length === attendu.length && crypto.timingSafeEqual(calcule, attendu);
  } catch (e) { return false; }
}

/* ===================================================================
   SESSIONS EN COURS
   =================================================================== */
const comptes = new Map();   // jeton -> { pseudo, solde, table, siege, vu, ... }

function nouveauJeton() { return crypto.randomBytes(16).toString('hex'); }

/* ===================================================================
   TABLES
   =================================================================== */
const NOMS_BOTS = ['Salvatore', 'Nadia', 'Marco', 'Enzo', 'Livia'];

function neuveTable(id, nom, mini) {
  return {
    id, nom, mini,
    sabot: neufSabot(),
    banque: [],
    places: [null, null, null],
    indexActif: -1,
    phase: 'attente',
    echeance: 0,
    prochaineCarte: 0,
    fileDistribution: [],
    cacheeRevelee: false,
    message: '',
    version: 1
  };
}

const tables = [
  neuveTable('majorelle', 'Jardin Majorelle', 0.01),
  neuveTable('palmeraie', 'Palmeraie Royale', 0.01)
];
function trouverTable(id) { return tables.find(t => t.id === id) || null; }

function tirer(table) {
  if (table.sabot.length < 40) table.sabot = neufSabot();
  return table.sabot.pop();
}
function touche(table) { table.version++; }
function dire(table, texte) { table.message = texte; }

/* ---------- les bots remplissent les places vides ---------- */
function garnirDeBots(table) {
  const humains = table.places.filter(p => p && p.type === 'humain').length;
  if (humains === 0) return;                       // table vide : pas de bots

  const pris = table.places.filter(p => p).map(p => p.nom);
  for (let i = 0; i < table.places.length; i++) {
    if (table.places[i]) continue;
    const libre = NOMS_BOTS.find(n => !pris.includes(n));
    if (!libre) break;
    pris.push(libre);
    table.places[i] = {
      type: 'bot', jeton: null, nom: libre,
      main: [], mise: 0, etat: 'attente',
      solde: sous(30 + crypto.randomInt(60)),
      resultat: null, pertesDeSuite: 0, provocation: false
    };
  }
}
function retirerBotsSiPlusPersonne(table) {
  const humains = table.places.filter(p => p && p.type === 'humain').length;
  if (humains > 0) return;
  table.places = [null, null, null];
  table.phase = 'attente';
  table.banque = [];
  table.indexActif = -1;
  table.message = '';
  touche(table);
}

/* ===================================================================
   DEROULEMENT D'UNE MANCHE
   =================================================================== */
function nouvelleManche(table) {
  table.banque = [];
  table.indexActif = -1;
  table.cacheeRevelee = false;
  table.fileDistribution = [];

  garnirDeBots(table);

  let quelquUnPeutJouer = false;
  for (const p of table.places) {
    if (!p) continue;
    p.main = [];
    p.mise = 0;
    p.resultat = null;
    p.provocation = false;
    // sans argent, on reste spectateur (on ne bloque pas la table)
    p.etat = p.solde >= 0.01 ? 'attente' : 'spectateur';
    if (p.etat === 'attente') quelquUnPeutJouer = true;
  }

  if (!quelquUnPeutJouer) {
    // tout le monde est fauche : on patiente, la table reste vivante
    table.phase = 'mise';
    table.echeance = Date.now() + DUREE_MISE;
    dire(table, 'La maison attend des joueurs solvables.');
    touche(table);
    return;
  }

  table.phase = 'mise';
  table.echeance = Date.now() + DUREE_MISE;
  dire(table, 'Faites vos jeux.');

  // les bots misent tout de suite
  for (const p of table.places) {
    if (p && p.type === 'bot' && p.etat === 'attente') {
      const m = Math.min(sous((crypto.randomInt(300) + 50) / 100), p.solde);
      p.mise = m;
      p.solde = sous(p.solde - m);
    }
  }
  touche(table);
}

function demarrerDistribution(table) {
  // mise automatique pour les humains qui n'ont rien pose
  for (const p of table.places) {
    if (p && p.type === 'humain' && p.etat === 'attente' && p.mise === 0) {
      const auto = Math.min(1, p.solde);
      if (auto >= 0.01) {
        p.mise = sous(auto);
        p.solde = sous(p.solde - p.mise);
        majSoldeCompte(p);
      } else {
        p.etat = 'spectateur';
      }
    }
  }

  const actifs = [];
  table.places.forEach((p, i) => { if (p && p.mise > 0) actifs.push(i); });

  if (actifs.length === 0) {                 // personne n'a mise : on relance
    table.phase = 'resultat';
    table.echeance = Date.now() + 1200;
    dire(table, 'Pas de mise. On recommence.');
    touche(table);
    return;
  }

  // ordre de distribution : joueurs puis banque, deux fois
  const file = [];
  for (let tour = 0; tour < 2; tour++) {
    for (const i of actifs) file.push({ cible: 'siege', index: i });
    file.push({ cible: 'banque' });
  }

  table.fileDistribution = file;
  table.phase = 'distribution';
  table.prochaineCarte = Date.now() + DELAI_CARTE;
  table.echeance = Date.now() + file.length * DELAI_CARTE + 4000;  // filet de securite
  dire(table, 'Les cartes sont en route.');
  touche(table);
}

function poserProchaineCarte(table) {
  const etape = table.fileDistribution.shift();
  if (!etape) return;

  if (etape.cible === 'banque') table.banque.push(tirer(table));
  else {
    const p = table.places[etape.index];
    if (p) p.main.push(tirer(table));
  }
  touche(table);

  if (table.fileDistribution.length === 0) {
    if (estBlackjack(table.banque)) { passerALaBanque(table); return; }
    table.indexActif = -1;
    tourSuivant(table);
  } else {
    table.prochaineCarte = Date.now() + DELAI_CARTE;
  }
}

function tourSuivant(table) {
  table.indexActif++;
  while (table.indexActif < table.places.length) {
    const p = table.places[table.indexActif];
    if (p && p.mise > 0 && p.etat === 'attente') break;
    table.indexActif++;
  }

  if (table.indexActif >= table.places.length) { passerALaBanque(table); return; }

  const p = table.places[table.indexActif];
  if (p.type === 'bot') {
    table.phase = 'bot';
    table.echeance = Date.now() + DELAI_BOT;
    dire(table, p.nom + ' réfléchit…');
  } else {
    table.phase = 'joueur';
    table.echeance = Date.now() + DUREE_TOUR;
    dire(table, 'À vous de décider.');
  }
  touche(table);
}

function jouerBot(table) {
  const p = table.places[table.indexActif];
  if (!p) { tourSuivant(table); return; }

  if (compter(p.main) < 17) {
    p.main.push(tirer(table));
    if (compter(p.main) > 21) {
      p.etat = 'saute';
      touche(table);
      tourSuivant(table);
    } else {
      table.echeance = Date.now() + DELAI_BOT;   // il continue de reflechir
      touche(table);
    }
  } else {
    p.etat = 'reste';
    touche(table);
    tourSuivant(table);
  }
}

function passerALaBanque(table) {
  table.phase = 'banque';
  table.cacheeRevelee = true;
  table.indexActif = -1;
  table.prochaineCarte = Date.now() + DELAI_BANQUE;
  table.echeance = Date.now() + 20000;           // filet de securite
  dire(table, 'La banque joue.');
  touche(table);
}

function banqueJoue(table) {
  const resteDesJoueurs = table.places.some(p => p && p.mise > 0 && p.etat !== 'saute');
  if (resteDesJoueurs && compter(table.banque) < 17) {
    table.banque.push(tirer(table));
    table.prochaineCarte = Date.now() + DELAI_BANQUE;
    touche(table);
    return;
  }
  conclure(table);
}

function conclure(table) {
  const tb = compter(table.banque);
  const bjBanque = estBlackjack(table.banque);

  for (const p of table.places) {
    if (!p || p.mise === 0) continue;
    const tm = compter(p.main);
    const bjMoi = estBlackjack(p.main);
    let texte = '', classe = '';

    if (tm > 21) {
      texte = 'Vous dépassez 21. La banque encaisse ' + eur(p.mise) + '.';
      classe = 'perdu';
    } else if (bjMoi && !bjBanque) {
      const g = sous(p.mise * 2.5);
      p.solde = sous(p.solde + g);
      texte = 'Blackjack ! Vous empochez ' + eur(g) + '.';
      classe = 'gagne';
    } else if (tb > 21) {
      const g = sous(p.mise * 2);
      p.solde = sous(p.solde + g);
      texte = 'La banque saute. Vous empochez ' + eur(g) + '.';
      classe = 'gagne';
    } else if (tm > tb) {
      const g = sous(p.mise * 2);
      p.solde = sous(p.solde + g);
      texte = tm + ' contre ' + tb + '. Vous empochez ' + eur(g) + '.';
      classe = 'gagne';
    } else if (tm < tb) {
      texte = tb + ' pour la banque. Vous perdez ' + eur(p.mise) + '.';
      classe = 'perdu';
    } else {
      p.solde = sous(p.solde + p.mise);
      texte = 'Égalité à ' + tm + '. Mise rendue.';
      classe = '';
    }

    p.resultat = { texte, classe };
    majSoldeCompte(p);

    // on inscrit la manche au carnet du joueur
    if (p.type === 'humain' && p.jeton) {
      const c = comptes.get(p.jeton);
      if (c) {
        c.mains++;
        if (classe === 'gagne')      c.gagnees++;
        else if (classe === 'perdu') c.perdues++;
        Carnet.enregistrer(c);
      }
    }

    // Don Koala se moque, uniquement chez le joueur qui a perdu deux fois
    if (classe === 'perdu') {
      p.pertesDeSuite = (p.pertesDeSuite || 0) + 1;
      if (p.pertesDeSuite >= 2) { p.provocation = true; p.pertesDeSuite = 0; }
    } else if (classe === 'gagne') {
      p.pertesDeSuite = 0;
    }
  }

  table.phase = 'resultat';
  table.echeance = Date.now() + DUREE_RESULTAT;
  dire(table, tb > 21 ? 'La banque saute.' : 'La maison remercie.');
  touche(table);
}

function eur(v) { return Number(v).toFixed(2).replace('.', ',') + ' €'; }

function majSoldeCompte(p) {
  if (p.type !== 'humain' || !p.jeton) return;
  const c = comptes.get(p.jeton);
  if (c) c.solde = p.solde;
}

/* ===================================================================
   LE BATTEMENT DE CŒUR — c'est lui qui empeche tout blocage
   =================================================================== */
function battement() {
  const now = Date.now();

  for (const table of tables) {
    // on libere les places des joueurs qui ne donnent plus de nouvelles
    let depart = false;
    table.places.forEach((p, i) => {
      if (!p || p.type !== 'humain') return;
      const c = comptes.get(p.jeton);
      if (!c || now - c.vu > ABSENCE_MAX) {
        if (c) { c.table = null; c.siege = -1; }
        table.places[i] = null;
        depart = true;
      }
    });
    if (depart) {
      touche(table);
      retirerBotsSiPlusPersonne(table);
      // si le joueur qui devait jouer vient de partir, on passe au suivant
      if ((table.phase === 'joueur' || table.phase === 'bot') && !table.places[table.indexActif]) {
        tourSuivant(table);
      }
    }

    switch (table.phase) {
      case 'attente':
        if (table.places.some(p => p && p.type === 'humain')) nouvelleManche(table);
        break;

      case 'mise':
        if (now >= table.echeance) demarrerDistribution(table);
        break;

      case 'distribution':
        if (now >= table.prochaineCarte) poserProchaineCarte(table);
        else if (now >= table.echeance) {           // filet : on ne reste jamais coince
          while (table.fileDistribution.length) poserProchaineCarte(table);
        }
        break;

      case 'joueur':
        if (now >= table.echeance) {                // le joueur n'a pas repondu : il reste
          const p = table.places[table.indexActif];
          if (p) p.etat = 'reste';
          touche(table);
          tourSuivant(table);
        }
        break;

      case 'bot':
        if (now >= table.echeance) jouerBot(table);
        break;

      case 'banque':
        if (now >= table.prochaineCarte) banqueJoue(table);
        else if (now >= table.echeance) conclure(table);
        break;

      case 'resultat':
        if (now >= table.echeance) nouvelleManche(table);
        break;
    }
  }
}
setInterval(battement, 200);

/* ===================================================================
   CE QUE VOIT UN JOUEUR
   =================================================================== */
function etatPour(table, jeton) {
  const moiIndex = table.places.findIndex(p => p && p.jeton === jeton);
  const moi = moiIndex >= 0 ? table.places[moiIndex] : null;
  const now = Date.now();

  const places = table.places.map((p, i) => {
    if (!p) return null;
    return {
      nom: p.nom,
      moi: i === moiIndex,
      bot: p.type === 'bot',
      mise: p.mise,
      main: p.main,
      etat: p.etat,
      total: compter(p.main)
    };
  });

  const banque = table.banque.map((c, i) =>
    (i === 1 && !table.cacheeRevelee) ? null : c            // la carte cachee n'est pas envoyee
  );

  let secondes = 0;
  if (table.phase === 'mise' || table.phase === 'joueur') {
    secondes = Math.max(0, Math.ceil((table.echeance - now) / 1000));
  }

  const provocation = !!(moi && moi.provocation);
  if (moi && moi.provocation) moi.provocation = false;       // on ne la montre qu'une fois

  return {
    version: table.version,
    table: table.id,
    nom: table.nom,
    phase: table.phase,
    secondes,
    indexActif: table.indexActif,
    cacheeRevelee: table.cacheeRevelee,
    banque,
    totalBanque: table.cacheeRevelee
      ? compter(table.banque)
      : (table.banque.length ? compter([table.banque[0]]) : 0),
    places,
    monIndex: moiIndex,
    monTour: moiIndex >= 0 && moiIndex === table.indexActif && table.phase === 'joueur',
    monSolde: moi ? moi.solde : (comptes.get(jeton) ? comptes.get(jeton).solde : 0),
    maMise: moi ? moi.mise : 0,
    peutDoubler: !!(moi && moi.main.length === 2 && moi.solde >= moi.mise),
    monResultat: moi ? moi.resultat : null,
    provocation,
    message: table.message,
    assis: moiIndex >= 0
  };
}

function resumeSalon() {
  return tables.map(t => ({
    id: t.id,
    nom: t.nom,
    mini: t.mini,
    phase: t.phase,
    places: t.places.map(p => p ? { nom: p.nom, bot: p.type === 'bot' } : null),
    joueurs: t.places.filter(p => p && p.type === 'humain').length
  }));
}

/* ===================================================================
   SERVEUR HTTP
   =================================================================== */
function corpsJSON(req) {
  return new Promise(resolve => {
    let data = '';
    req.on('data', c => {
      data += c;
      if (data.length > 1e5) { data = ''; req.destroy(); }
    });
    req.on('end', () => {
      try { resolve(JSON.parse(data || '{}')); }
      catch { resolve({}); }
    });
  });
}
function repondre(res, code, objet) {
  const corps = JSON.stringify(objet);
  res.writeHead(code, {
    'Content-Type': 'application/json; charset=utf-8',
    'Cache-Control': 'no-store'
  });
  res.end(corps);
}

const TYPES = {
  '.html': 'text/html; charset=utf-8',
  '.js':   'text/javascript; charset=utf-8',
  '.css':  'text/css; charset=utf-8',
  '.jpg':  'image/jpeg', '.jpeg': 'image/jpeg',
  '.png':  'image/png',  '.svg':  'image/svg+xml',
  '.ico':  'image/x-icon'
};

function servirFichier(res, chemin) {
  fs.readFile(chemin, (err, contenu) => {
    if (err) { res.writeHead(404); res.end('Introuvable'); return; }
    const type = TYPES[path.extname(chemin).toLowerCase()] || 'application/octet-stream';
    res.writeHead(200, { 'Content-Type': type, 'Cache-Control': 'no-cache' });
    res.end(contenu);
  });
}

/* ---------- on retrouve le joueur a chaque appel ---------- */
function identifier(jeton) {
  const c = comptes.get(jeton);
  if (!c) return null;
  c.vu = Date.now();
  return c;
}
function siegeDe(compte) {
  if (!compte || !compte.table) return null;
  const table = trouverTable(compte.table);
  if (!table) return null;
  const p = table.places.find(x => x && x.jeton === compte.jetonRef);
  return p ? { table, p } : { table, p: null };
}

const serveur = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://x');
  const route = url.pathname;

  /* ---------------- API ---------------- */
  if (route.startsWith('/api/')) {

    // --- créer un compte ---
    if (route === '/api/inscription' && req.method === 'POST') {
      const body   = await corpsJSON(req);
      const pseudo = String(body.pseudo || '').trim().slice(0, 16);
      const mdp    = String(body.motDePasse || '');

      if (pseudo.length < 3) {
        return repondre(res, 400, { erreur: 'Choisissez un pseudo d’au moins 3 caractères.' });
      }
      if (!/^[\p{L}\p{N} _.'-]+$/u.test(pseudo)) {
        return repondre(res, 400, { erreur: 'Pseudo : lettres, chiffres et espaces uniquement.' });
      }
      if (mdp.length < 4) {
        return repondre(res, 400, { erreur: 'Mot de passe trop court (4 caractères minimum).' });
      }

      const pseudoBas = pseudo.toLowerCase();
      if (await Carnet.lire(pseudoBas)) {
        return repondre(res, 409, { erreur: 'Ce pseudo est déjà pris. Choisissez-en un autre.' });
      }

      const fiche = {
        pseudoBas, pseudo,
        motDePasse: await chiffrer(mdp),
        solde: SOLDE_DEPART,
        mains: 0, gagnees: 0, perdues: 0, poissons: 0,
        penaltys: 0, buts: 0, defaitesPenalty: 0, periphs: 0, portes: 0, periph: null, perso: null,
        voiturePremium: false
      };
      if (!await Carnet.creer(fiche)) {
        return repondre(res, 409, { erreur: 'Ce pseudo est déjà pris. Choisissez-en un autre.' });
      }
      return repondre(res, 200, ouvrirSession(fiche));
    }

    // --- se connecter ---
    if (route === '/api/connexion' && req.method === 'POST') {
      const body   = await corpsJSON(req);
      const pseudo = String(body.pseudo || '').trim();
      const mdp    = String(body.motDePasse || '');

      if (!pseudo || !mdp) {
        return repondre(res, 400, { erreur: 'Renseignez votre pseudo et votre mot de passe.' });
      }
      const fiche = await Carnet.lire(pseudo.toLowerCase());
      if (!fiche || !await motDePasseJuste(mdp, fiche.motDePasse)) {
        return repondre(res, 401, { erreur: 'Pseudo ou mot de passe incorrect.' });
      }
      return repondre(res, 200, ouvrirSession(fiche));
    }

    const jeton  = url.searchParams.get('jeton') || (req.headers['x-jeton'] || '');
    let   compte = identifier(jeton);
    let   body   = {};
    if (req.method === 'POST') {
      body = await corpsJSON(req);
      if (!compte && body.jeton) compte = identifier(body.jeton);
    }
    if (!compte) return repondre(res, 401, { erreur: 'session expiree' });

    // --- liste des tables ---
    if (route === '/api/salon') {
      return repondre(res, 200, { tables: resumeSalon(), solde: compte.solde });
    }

    // --- s'asseoir ---
    if (route === '/api/asseoir' && req.method === 'POST') {
      const table = trouverTable(String(body.table || ''));
      if (!table) return repondre(res, 404, { erreur: 'table inconnue' });

      // on quitte l'ancienne table le cas echeant
      quitterTable(compte);

      // on chasse un bot si besoin pour faire de la place
      let place = table.places.findIndex(p => !p);
      if (place < 0) place = table.places.findIndex(p => p && p.type === 'bot');
      if (place < 0) return repondre(res, 409, { erreur: 'table complete' });

      table.places[place] = {
        type: 'humain', jeton: compte.jetonRef, nom: compte.pseudo,
        main: [], mise: 0,
        etat: (table.phase === 'mise' || table.phase === 'attente') ? 'attente' : 'spectateur',
        solde: compte.solde, resultat: null, pertesDeSuite: 0, provocation: false
      };
      compte.table = table.id;
      compte.siege = place;
      garnirDeBots(table);
      if (table.phase === 'attente') nouvelleManche(table);
      touche(table);
      return repondre(res, 200, etatPour(table, compte.jetonRef));
    }

    // --- quitter ---
    if (route === '/api/quitter' && req.method === 'POST') {
      quitterTable(compte);
      return repondre(res, 200, { ok: true, solde: compte.solde });
    }

    // --- etat de la table (appele en boucle par le jeu) ---
    if (route === '/api/etat') {
      if (!compte.table) return repondre(res, 200, { assis: false, solde: compte.solde });
      const table = trouverTable(compte.table);
      if (!table) return repondre(res, 200, { assis: false, solde: compte.solde });
      return repondre(res, 200, etatPour(table, compte.jetonRef));
    }

    // --- miser ---
    if (route === '/api/miser' && req.method === 'POST') {
      const info = siegeDe(compte);
      if (!info || !info.p) return repondre(res, 409, { erreur: 'pas a table' });
      const { table, p } = info;
      if (table.phase !== 'mise') return repondre(res, 409, { erreur: 'trop tard' });
      if (p.etat !== 'attente')   return repondre(res, 409, { erreur: 'spectateur' });

      let v = Number(body.mise);
      if (!isFinite(v) || v < 0.01) return repondre(res, 400, { erreur: 'mise trop faible' });
      v = sous(v);
      if (v > p.solde + 1e-9) return repondre(res, 400, { erreur: 'solde insuffisant' });

      p.mise  = v;
      p.solde = sous(p.solde - v);
      majSoldeCompte(p);
      touche(table);
      return repondre(res, 200, etatPour(table, compte.jetonRef));
    }

    // --- carte / rester / doubler ---
    if (route === '/api/action' && req.method === 'POST') {
      const info = siegeDe(compte);
      if (!info || !info.p) return repondre(res, 409, { erreur: 'pas a table' });
      const { table, p } = info;
      const monIndex = table.places.indexOf(p);
      if (table.phase !== 'joueur' || table.indexActif !== monIndex) {
        return repondre(res, 409, { erreur: 'pas votre tour' });
      }

      const action = String(body.action || '');

      if (action === 'carte') {
        p.main.push(tirer(table));
        const t = compter(p.main);
        if (t > 21)       { p.etat = 'saute'; touche(table); tourSuivant(table); }
        else if (t === 21){ p.etat = 'reste'; touche(table); tourSuivant(table); }
        else              { table.echeance = Date.now() + DUREE_TOUR; touche(table); }

      } else if (action === 'rester') {
        p.etat = 'reste';
        touche(table);
        tourSuivant(table);

      } else if (action === 'doubler') {
        if (p.main.length !== 2 || p.solde < p.mise) {
          return repondre(res, 400, { erreur: 'doublement impossible' });
        }
        p.solde = sous(p.solde - p.mise);
        p.mise  = sous(p.mise * 2);
        majSoldeCompte(p);
        p.main.push(tirer(table));
        p.etat = compter(p.main) > 21 ? 'saute' : 'reste';
        touche(table);
        tourSuivant(table);

      } else {
        return repondre(res, 400, { erreur: 'action inconnue' });
      }

      return repondre(res, 200, etatPour(table, compte.jetonRef));
    }

    // --- une prise à la pêche : c'est le serveur qui crédite ---
    if (route === '/api/peche' && req.method === 'POST') {
      compte.solde    = sous(compte.solde + 1);
      compte.poissons = compte.poissons + 1;
      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
      Carnet.enregistrer(compte);
      return repondre(res, 200, { solde: compte.solde, poissons: compte.poissons });
    }

    // --- l'apparence du personnage ---
    if (route === '/api/perso' && req.method === 'POST') {
      try { compte.perso = JSON.stringify(body.perso || {}).slice(0, 400); } catch (e) {}
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true });
    }

    /* ===============================================================
       LE PENALTY
       ---------------------------------------------------------------
       Tout se decide ici : la reussite du tir, le cote choisi par le
       gardien, le montant gagne. La page ne fait que montrer le
       resultat. Un joueur qui bidouillerait sa page ne gagnerait rien.
       =============================================================== */

    // --- on pose sa mise et la serie commence ---
    if (route === '/api/penalty-demarrer' && req.method === 'POST') {
      if (compte.penalty) {
        return repondre(res, 409, { erreur: 'Une série est déjà en cours.' });
      }
      const mise = sous(Number(body.mise) || 0);
      if (!(mise >= MISE_MINI_PENALTY)) {
        return repondre(res, 400, { erreur: 'Mise minimum : 0,10 €.' });
      }
      if (mise > compte.solde) {
        return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      }

      compte.solde = sous(compte.solde - mise);        // la mise part tout de suite
      compte.penalty = { mise: mise, palier: 0 };

      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
      Carnet.enregistrer(compte);

      return repondre(res, 200, {
        ok: true, mise: mise, palier: 0, solde: compte.solde,
        echelle: ECHELLE_PENALTY
      });
    }

    // --- on tire ---
    if (route === '/api/penalty-tirer' && req.method === 'POST') {
      const serie = compte.penalty;
      if (!serie) return repondre(res, 409, { erreur: 'Aucune série en cours.' });

      const zone = Math.max(0, Math.min(ZONES_PENALTY - 1, Number(body.zone) | 0));

      /* Le petit secret : apres deux echecs d'affilee, viser la tete du
         gardien donne un but a coup sur. C'est le serveur qui verifie la
         condition, pas la page : impossible de s'en servir a volonte. */
      const viseLaTete = body.tete === true;
      const secret = viseLaTete && (compte.defaitesPenalty | 0) >= DEFAITES_SECRET;

      // le sort en est jete
      const but = secret || crypto.randomInt(10000) < CHANCE_BUT;

      // le gardien plonge la ou il faut pour que l'image colle au resultat
      let zoneGardien;
      if (secret)   zoneGardien = -1;          // il ne bouge pas, il encaisse
      else if (but) { do { zoneGardien = crypto.randomInt(ZONES_PENALTY); } while (zoneGardien === zone); }
      else          zoneGardien = zone;

      compte.penaltys = compte.penaltys + 1;

      if (!but) {
        // rate : la mise est perdue, la serie s'arrete
        const perdu = serie.mise;
        compte.penalty = null;
        compte.defaitesPenalty = (compte.defaitesPenalty | 0) + 1;
        Carnet.enregistrer(compte);
        return repondre(res, 200, {
          but: false, zone: zone, zoneGardien: zoneGardien,
          fini: true, perdu: perdu, palier: 0,
          multiplicateur: 0, gainPotentiel: 0, solde: compte.solde
        });
      }

      // but : on monte d'un cran
      compte.buts = compte.buts + 1;
      compte.defaitesPenalty = 0;
      serie.palier = serie.palier + 1;
      const multiplicateur = ECHELLE_PENALTY[serie.palier - 1];
      const gainPotentiel  = sous(serie.mise * multiplicateur);
      const auSommet       = serie.palier >= ECHELLE_PENALTY.length;

      if (auSommet) {
        // au sommet de l'echelle, on encaisse d'office
        compte.solde   = sous(compte.solde + gainPotentiel);
        compte.penalty = null;
        const info = siegeDe(compte);
        if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
        Carnet.enregistrer(compte);
        return repondre(res, 200, {
          but: true, zone: zone, zoneGardien: zoneGardien, secret: secret,
          fini: true, sommet: true, encaisse: gainPotentiel,
          palier: ECHELLE_PENALTY.length, multiplicateur: multiplicateur,
          gainPotentiel: gainPotentiel, solde: compte.solde
        });
      }

      Carnet.enregistrer(compte);
      return repondre(res, 200, {
        but: true, zone: zone, zoneGardien: zoneGardien, secret: secret,
        fini: false, palier: serie.palier,
        multiplicateur: multiplicateur, gainPotentiel: gainPotentiel,
        suivant: ECHELLE_PENALTY[serie.palier],
        solde: compte.solde
      });
    }

    // --- on encaisse et on s'arrete la ---
    if (route === '/api/penalty-encaisser' && req.method === 'POST') {
      const serie = compte.penalty;
      if (!serie) return repondre(res, 409, { erreur: 'Aucune série en cours.' });
      if (serie.palier < 1) {
        return repondre(res, 400, { erreur: 'Marquez au moins un but avant d’encaisser.' });
      }

      const gain = sous(serie.mise * ECHELLE_PENALTY[serie.palier - 1]);
      compte.solde   = sous(compte.solde + gain);
      compte.penalty = null;

      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
      Carnet.enregistrer(compte);

      return repondre(res, 200, { ok: true, gain: gain, solde: compte.solde });
    }

    /* ===============================================================
       LE JEU DU PERIPH
       =============================================================== */

    // --- on pose sa mise et la course commence ---
    if (route === '/api/periph-demarrer' && req.method === 'POST') {
      const mise = sous(Number(body.mise) || 0);
      if (!(mise >= MISE_MINI_PERIPH)) {
        return repondre(res, 400, { erreur: 'Mise minimum : 0,10 €.' });
      }
      if (mise > MISE_MAXI_PERIPH) {
        return repondre(res, 400, { erreur: 'Mise maximum : 100,00 €.' });
      }
      if (mise > compte.solde) {
        return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      }
      // la voiture premium n'est utilisable que si elle a ete achetee
      const voiture = (Number(body.voiture) | 0) === VOITURE_PREMIUM_INDICE && compte.voiturePremium
        ? VOITURE_PREMIUM_INDICE : bornerVoitureNormale(body.voiture);

      // une course abandonnee en route est simplement perdue : on repart proprement
      compte.solde  = sous(compte.solde - mise);
      compte.periph = { mise: mise, palier: 0, depart: Date.now(), voiture: voiture };
      compte.periphs = (compte.periphs | 0) + 1;

      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
      Carnet.enregistrer(compte);

      return repondre(res, 200, {
        ok: true, mise: mise, palier: 0, solde: compte.solde, voiture: voiture,
        echelle: ECHELLE_PERIPH, longueurs: LONGUEURS_PERIPH
      });
    }

    // --- la boutique : on achete la voiture premium ---
    if (route === '/api/periph-acheter-voiture' && req.method === 'POST') {
      if (compte.voiturePremium) {
        return repondre(res, 409, { erreur: 'Vous avez déjà cette voiture.' });
      }
      if (compte.periph) {
        return repondre(res, 409, { erreur: 'Terminez votre course avant d’aller à la boutique.' });
      }
      if (compte.solde < PRIX_VOITURE_PREMIUM) {
        return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      }
      compte.solde = sous(compte.solde - PRIX_VOITURE_PREMIUM);
      compte.voiturePremium = true;

      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
      Carnet.enregistrer(compte);

      return repondre(res, 200, { ok: true, solde: compte.solde, voiturePremium: true });
    }

    // --- on franchit une porte ---
    if (route === '/api/periph-porte' && req.method === 'POST') {
      const course = compte.periph;
      if (!course) return repondre(res, 409, { erreur: 'Aucune course en cours.' });
      if (course.palier >= ECHELLE_PERIPH.length) {
        return repondre(res, 409, { erreur: 'Course déjà terminée.' });
      }
      // la porte annoncee doit etre la suivante, et pas trop tot :
      // meme a fond, il faut le temps de parcourir la distance
      const suivant   = course.palier + 1;
      const vitesseMax = course.voiture === VOITURE_PREMIUM_INDICE
        ? VITESSE_MAX_PERIPH_PREMIUM : VITESSE_MAX_PERIPH;
      const attendu  = distancePeriph(suivant) / vitesseMax * MARGE_TEMPS;
      const ecoule   = (Date.now() - course.depart) / 1000;
      if (ecoule < attendu) {
        compte.periph = null;
        Carnet.enregistrer(compte);
        return repondre(res, 400, { erreur: 'Course invalide.' });
      }

      course.palier  = suivant;
      compte.portes  = (compte.portes | 0) + 1;
      const gain     = sous(course.mise * ECHELLE_PERIPH[suivant - 1]);
      const fini     = suivant >= ECHELLE_PERIPH.length;

      if (fini) {                                   // Saint-Denis : on encaisse d'office
        compte.solde  = sous(compte.solde + gain);
        compte.periph = null;
        const info2 = siegeDe(compte);
        if (info2 && info2.p) { info2.p.solde = compte.solde; touche(info2.table); }
      }
      Carnet.enregistrer(compte);

      return repondre(res, 200, {
        ok: true, palier: suivant, porte: NOMS_PERIPH[suivant - 1],
        gainPotentiel: gain, fini: fini,
        suivante: fini ? null : NOMS_PERIPH[suivant],
        gainSuivant: fini ? null : sous(course.mise * ECHELLE_PERIPH[suivant]),
        solde: compte.solde
      });
    }

    // --- on encaisse ---
    if (route === '/api/periph-encaisser' && req.method === 'POST') {
      const course = compte.periph;
      if (!course) return repondre(res, 409, { erreur: 'Aucune course en cours.' });
      if (course.palier < 1) {
        return repondre(res, 400, { erreur: 'Franchissez au moins une porte.' });
      }
      const gain = sous(course.mise * ECHELLE_PERIPH[course.palier - 1]);
      compte.solde  = sous(compte.solde + gain);
      compte.periph = null;

      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
      Carnet.enregistrer(compte);

      return repondre(res, 200, { ok: true, gain: gain, solde: compte.solde });
    }

    // --- la voiture est detruite, ou on s'est fait doubler ---
    if (route === '/api/periph-perdu' && req.method === 'POST') {
      compte.periph = null;
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, solde: compte.solde });
    }

    // --- ma fiche (écran profil) ---
    if (route === '/api/moi') {
      return repondre(res, 200, {
        pseudo:   compte.pseudo,
        solde:    compte.solde,
        mains:    compte.mains,
        gagnees:  compte.gagnees,
        perdues:  compte.perdues,
        poissons: compte.poissons,
        penaltys: compte.penaltys,
        buts:     compte.buts,
        defaites: compte.defaitesPenalty | 0,
        periphs:  compte.periphs | 0,
        portes:   compte.portes  | 0,
        voiturePremium: !!compte.voiturePremium,
        penalty:  compte.penalty
          ? { mise: compte.penalty.mise, palier: compte.penalty.palier }
          : null,
        periph:   compte.periph
          ? { mise: compte.periph.mise, palier: compte.periph.palier }
          : null
      });
    }

    return repondre(res, 404, { erreur: 'route inconnue' });
  }

  /* ---------------- fichiers du site ---------------- */
  let fichier = route === '/' ? '/index.html' : route;
  fichier = path.normalize(fichier).replace(/^(\.\.[\/\\])+/, '');

  // les fichiers de travail ne sont pas visibles depuis le site
  const nom = path.basename(fichier).toLowerCase();
  const PRIVES = ['serveur.js', 'package.json', 'package-lock.json', 'lisez-moi.txt'];
  if (PRIVES.indexOf(nom) >= 0 || nom.charAt(0) === '.') {
    res.writeHead(404); res.end('Introuvable'); return;
  }

  const chemin = path.join(DOSSIER, fichier);
  if (!chemin.startsWith(DOSSIER)) { res.writeHead(403); res.end('Interdit'); return; }
  servirFichier(res, chemin);
});

/* Ouvre une session pour un joueur reconnu. Un joueur ne peut être
   connecté qu'une fois : ouvrir une session ferme la précédente, sinon
   deux appareils feraient diverger le même solde. */
function ouvrirSession(fiche) {
  for (const [j, c] of comptes) {
    if (c.pseudoBas === fiche.pseudoBas) { quitterTable(c); comptes.delete(j); }
  }

  const jeton = nouveauJeton();
  const compte = {
    jetonRef: jeton,
    pseudo:    fiche.pseudo,
    pseudoBas: fiche.pseudoBas,
    solde:     sous(Number(fiche.solde)),
    mains:     fiche.mains    | 0,
    gagnees:   fiche.gagnees  | 0,
    perdues:   fiche.perdues  | 0,
    poissons:  fiche.poissons | 0,
    penaltys:  fiche.penaltys | 0,
    periphs:   fiche.periphs  | 0,
    portes:    fiche.portes   | 0,
    buts:      fiche.buts     | 0,
    defaitesPenalty: fiche.defaitesPenalty | 0,
    perso:     fiche.perso || null,
    voiturePremium: !!fiche.voiturePremium,
    penalty: null,                       // aucune serie de penaltys en cours
    periph:  null,                       // aucune course de periph en cours
    table: null, siege: -1, vu: Date.now()
  };
  comptes.set(jeton, compte);

  return {
    jeton,
    pseudo:   compte.pseudo,
    solde:    compte.solde,
    mains:    compte.mains,
    gagnees:  compte.gagnees,
    perdues:  compte.perdues,
    poissons: compte.poissons,
    penaltys: compte.penaltys,
    periphs:  compte.periphs | 0,
    portes:   compte.portes  | 0,
    buts:     compte.buts,
    perso:    compte.perso,
    voiturePremium: compte.voiturePremium,
    creeLe:   fiche.creeLe || null
  };
}

function quitterTable(compte) {
  if (!compte.table) return;
  const table = trouverTable(compte.table);
  compte.table = null;
  compte.siege = -1;
  if (!table) return;

  const i = table.places.findIndex(p => p && p.jeton === compte.jetonRef);
  if (i >= 0) {
    table.places[i] = null;
    touche(table);
    if ((table.phase === 'joueur' || table.phase === 'bot') && table.indexActif === i) {
      tourSuivant(table);
    }
    retirerBotsSiPlusPersonne(table);
  }
}

Carnet.demarrer().then(() => {
  serveur.listen(PORT, () => {
    console.log('Casino Messina — le salon est ouvert sur le port ' + PORT);
  });
});
