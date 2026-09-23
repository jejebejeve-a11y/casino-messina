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
const DUREE_MISE      = 12000;  // temps pour miser
const DUREE_TOUR      = 15000;  // temps pour jouer son tour
const DUREE_RESULTAT  = 6000;   // affichage du resultat avant la manche suivante
const DELAI_CARTE     = 560;    // entre deux cartes distribuees
const DELAI_BANQUE    = 950;    // entre deux cartes de la banque
const DELAI_BOT       = 1300;   // temps de reflexion d'un bot
const CHAT_MAX        = 60;     // messages de chat conserves par table
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

/* ---------- le periph en multijoueur ----------
   Une file d'attente toute simple : des qu'un deuxieme joueur reel la
   rejoint, un compte a rebours de dix secondes demarre pour tout le
   monde. S'il redescend a moins de deux avant la fin, on annule, sans
   frais pour personne. Au top depart, chacun est debite et sa course
   demarre exactement comme en solo (meme fonction interne). Un petit
   groupe de course garde ensuite, pendant la course, la progression
   annoncee par chacun : ca ne sert qu'a dessiner la voiture des autres
   joueurs, jamais a calculer un gain (ca, c'est toujours les routes
   /api/periph-porte, /api/periph-encaisser, /api/periph-perdu, inchangees). */
const DUREE_ATTENTE_PERIPH_MULTI = 10000;
const EXPIRATION_COURSE_MULTI    = 5 * 60000;   // filet de securite

/* ---------- Tower Rush ----------
   Un etage se balance sous la grue ; le joueur appuie pour le lacher.
   Comme pour le periph, la balancoire s'anime dans la page pour que ce
   soit fluide, mais le moment exact du lacher n'est jamais cru sur
   parole : ce fichier garde l'heure a laquelle CHAQUE balancement a
   commence (compte.tower.swingStart) et recalcule lui-meme, a la
   milliseconde pres, ou en etait le balancement quand la demande est
   arrivee. La precision, le multiplicateur et le risque d'effondrement
   sont donc entierement decides ici, jamais par la page. */
const MISE_MINI_TOWER = 0.10;
const MISE_MAXI_TOWER = 500;

function towerAmpFor(n)    { return Math.max(17, 48 - n * 2.1); }
function towerPeriodFor(n) { return Math.max(0.68, 1.5 - n * 0.04); }
function towerRand(a, b) { return a + Math.random() * (b - a); }
function towerClamp(v, a, b) { return Math.max(a, Math.min(b, v)); }

function towerRollFactor(n, errRatio) {
  if (n === 0) {
    let f0 = (Math.random() < 0.63) ? towerRand(0.45, 0.99) : towerRand(1.0, 1.9);
    if (errRatio < 0.1 && Math.random() < 0.35) f0 = Math.max(f0, towerRand(1.8, 2.6));
    return Math.min(f0, 7);
  }
  const subChance = towerClamp(0.55 - n * 0.045, 0.12, 0.55);
  let f = (Math.random() < subChance) ? towerRand(0.5, 1.0) : towerRand(1.0, 1 + 0.4 * n);
  if (errRatio < 0.1 && Math.random() < 0.4) f = Math.max(f, towerRand(1.8, 2.6 + 0.3 * n));
  return Math.min(f, 7);
}

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
  indexMemoire: new Map(),   // repli pour l'index de tous les joueurs

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
      roulettes: compte.roulettes | 0,
      voiturePremium: !!compte.voiturePremium,
      perso:     compte.perso || ancienne.perso || null,
      codesUtilises: Array.isArray(compte.codesUtilises) ? compte.codesUtilises : (ancienne.codesUtilises || []),
      vuLe:      new Date().toISOString()
    });
    this.memoire.set(compte.pseudoBas, fiche);

    if (!this.pret) return;
    this.commande(['SET', 'joueur:' + compte.pseudoBas, JSON.stringify(fiche)])
      .catch(e => console.log('Carnet : enregistrement impossible (' + e.message + ')'));
  },

  // Tient un seul index { pseudoBas: {pseudo, creeLe, vuLe} } pour pouvoir
  // lister tous les joueurs deja crees (le code "RS6" s'en sert). On ne
  // le touche qu'a la creation du compte et a la connexion, jamais a
  // chaque appel : inutile de solliciter la base pour ca.
  async indexerJoueur(pseudoBas, pseudo) {
    const maintenant = new Date().toISOString();
    if (!this.pret) {
      const ancienne = this.indexMemoire.get(pseudoBas) || {};
      this.indexMemoire.set(pseudoBas, { pseudo, creeLe: ancienne.creeLe || maintenant, vuLe: maintenant });
      return;
    }
    try {
      const r = await this.commande(['GET', 'index:joueurs']);
      let index = {};
      if (r && r.result) { try { index = JSON.parse(r.result); } catch (e) { index = {}; } }
      const ancienne = index[pseudoBas] || {};
      index[pseudoBas] = { pseudo, creeLe: ancienne.creeLe || maintenant, vuLe: maintenant };
      await this.commande(['SET', 'index:joueurs', JSON.stringify(index)]);
    } catch (e) {
      console.log('Carnet : mise à jour de l’index impossible (' + e.message + ')');
      const ancienne = this.indexMemoire.get(pseudoBas) || {};
      this.indexMemoire.set(pseudoBas, { pseudo, creeLe: ancienne.creeLe || maintenant, vuLe: maintenant });
    }
  },

  // Certains comptes ont ete crees avant que cet index existe (ou n'ont
  // jamais reserve pour se reconnecter depuis) : on les retrouve tous en
  // listant les fiches "joueur:*" directement, et on reconstruit l'index
  // en entier a partir d'elles pour que la date "vu" reste juste (la
  // fiche, elle, est mise a jour a chaque partie jouee).
  async reconcilierIndex() {
    if (!this.pret) return;
    try {
      const r = await this.commande(['KEYS', 'joueur:*']);
      const cles = (r && Array.isArray(r.result)) ? r.result : [];
      if (!cles.length) return;
      const index = {};
      for (const cle of cles) {
        const pseudoBas = cle.slice('joueur:'.length);
        if (!pseudoBas) continue;
        try {
          const rf = await this.commande(['GET', cle]);
          if (!rf || !rf.result) continue;
          const fiche = JSON.parse(rf.result);
          index[pseudoBas] = {
            pseudo: fiche.pseudo || pseudoBas,
            creeLe: fiche.creeLe || null,
            vuLe:   fiche.vuLe   || fiche.creeLe || null
          };
        } catch (e) { /* une fiche illisible ne doit pas bloquer les autres */ }
      }
      await this.commande(['SET', 'index:joueurs', JSON.stringify(index)]);
    } catch (e) {
      console.log('Carnet : reconciliation de l’index impossible (' + e.message + ')');
    }
  },

  async listerJoueurs() {
    if (!this.pret) {
      return Array.from(this.indexMemoire.entries()).map(([pseudoBas, v]) => Object.assign({ pseudoBas }, v));
    }
    try {
      await this.reconcilierIndex();
      const r = await this.commande(['GET', 'index:joueurs']);
      let index = {};
      if (r && r.result) { try { index = JSON.parse(r.result); } catch (e) { index = {}; } }
      return Object.keys(index).map(pseudoBas => Object.assign({ pseudoBas }, index[pseudoBas]));
    } catch (e) {
      console.log('Carnet : lecture de l’index impossible (' + e.message + ')');
      return Array.from(this.indexMemoire.entries()).map(([pseudoBas, v]) => Object.assign({ pseudoBas }, v));
    }
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

function neuveTable(id, nom, mini, skin) {
  return {
    id, nom, mini, skin: skin || 'vert',
    sabot: neufSabot(),
    banque: [],
    places: [null, null, null],
    indexActif: -1,
    mainActive: 0,
    phase: 'attente',
    echeance: 0,
    prochaineCarte: 0,
    fileDistribution: [],
    cacheeRevelee: false,
    message: '',
    chat: [],
    chatId: 0,
    version: 1
  };
}

const tables = [
  neuveTable('majorelle', 'Jardin Majorelle', 0.01, 'vert'),
  neuveTable('palmeraie', 'Palmeraie Royale', 0.01, 'or')
];
function trouverTable(id) { return tables.find(t => t.id === id) || null; }

function tirer(table) {
  if (table.sabot.length < 40) table.sabot = neufSabot();
  return table.sabot.pop();
}
function touche(table) { table.version++; }
function dire(table, texte) { table.message = texte; }

/* ---------- une main de blackjack (une place peut en avoir deux
   apres un partage/split) ---------- */
function neuveMain(mise) {
  return { cartes: [], mise: mise || 0, etat: 'attente', resultat: null };
}

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
      mains: [neuveMain(0)], etat: 'attente',
      solde: sous(30 + crypto.randomInt(60)),
      resultat: null, pertesDeSuite: 0, provocation: false, soldeVisible: true
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
  table.mainActive = 0;
  table.message = '';
  table.chat = [];
  table.chatId = 0;
  touche(table);
}

/* ===================================================================
   DEROULEMENT D'UNE MANCHE
   =================================================================== */
function nouvelleManche(table) {
  table.banque = [];
  table.indexActif = -1;
  table.mainActive = 0;
  table.cacheeRevelee = false;
  table.fileDistribution = [];

  garnirDeBots(table);

  let quelquUnPeutJouer = false;
  for (const p of table.places) {
    if (!p) continue;
    p.mains = [neuveMain(0)];
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
      p.mains[0].mise = m;
      p.solde = sous(p.solde - m);
    }
  }
  touche(table);
}

function demarrerDistribution(table) {
  // mise automatique pour les humains qui n'ont rien pose
  for (const p of table.places) {
    if (p && p.type === 'humain' && p.etat === 'attente' && p.mains[0].mise === 0) {
      const auto = Math.min(1, p.solde);
      if (auto >= 0.01) {
        p.mains[0].mise = sous(auto);
        p.solde = sous(p.solde - p.mains[0].mise);
        majSoldeCompte(p);
      } else {
        p.etat = 'spectateur';
      }
    }
  }

  const actifs = [];
  table.places.forEach((p, i) => { if (p && p.mains[0].mise > 0) actifs.push(i); });

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
    if (p) p.mains[0].cartes.push(tirer(table));
  }
  touche(table);

  if (table.fileDistribution.length === 0) {
    if (estBlackjack(table.banque)) { passerALaBanque(table); return; }
    table.indexActif = -1;
    table.mainActive = 0;
    tourSuivant(table);
  } else {
    table.prochaineCarte = Date.now() + DELAI_CARTE;
  }
}

/* ---------- fait demarrer le chrono / le message pour la place et
   la main actuellement actives ---------- */
function demarrerTourDe(table, p) {
  if (p.type === 'bot') {
    table.phase = 'bot';
    table.echeance = Date.now() + DELAI_BOT;
    dire(table, p.nom + ' réfléchit…');
  } else {
    table.phase = 'joueur';
    table.echeance = Date.now() + DUREE_TOUR;
    dire(table, p.mains.length > 1
      ? 'À vous de décider (main ' + (table.mainActive + 1) + ').'
      : 'À vous de décider.');
  }
  touche(table);
}

/* ---------- avance au prochain joueur/main a jouer. Gere le fait
   qu'une place partagee (split) a deux mains a jouer l'une apres
   l'autre avant de passer a la place suivante. ---------- */
function tourSuivant(table) {
  // la place courante a-t-elle une deuxieme main encore a jouer ?
  const courant = table.indexActif >= 0 ? table.places[table.indexActif] : null;
  if (courant && table.mainActive === 0 && courant.mains.length > 1 &&
      courant.mains[1].etat === 'attente') {
    table.mainActive = 1;
    demarrerTourDe(table, courant);
    return;
  }

  table.indexActif++;
  table.mainActive = 0;
  while (table.indexActif < table.places.length) {
    const p = table.places[table.indexActif];
    if (p && p.mains[0].mise > 0 && p.mains[0].etat === 'attente') break;
    table.indexActif++;
  }

  if (table.indexActif >= table.places.length) { passerALaBanque(table); return; }
  demarrerTourDe(table, table.places[table.indexActif]);
}

function jouerBot(table) {
  const p = table.places[table.indexActif];
  if (!p) { tourSuivant(table); return; }
  const m = p.mains[0];

  if (compter(m.cartes) < 17) {
    m.cartes.push(tirer(table));
    if (compter(m.cartes) > 21) {
      m.etat = 'saute';
      touche(table);
      tourSuivant(table);
    } else {
      table.echeance = Date.now() + DELAI_BOT;   // il continue de reflechir
      touche(table);
    }
  } else {
    m.etat = 'reste';
    touche(table);
    tourSuivant(table);
  }
}

function passerALaBanque(table) {
  table.phase = 'banque';
  table.cacheeRevelee = true;
  table.indexActif = -1;
  table.mainActive = 0;
  table.prochaineCarte = Date.now() + DELAI_BANQUE;
  table.echeance = Date.now() + 20000;           // filet de securite
  dire(table, 'La banque joue.');
  touche(table);
}

function banqueJoue(table) {
  const resteDesJoueurs = table.places.some(p => p && p.mains.some(m => m.mise > 0 && m.etat !== 'saute'));
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
    if (!p) continue;
    const misesJouees = p.mains.filter(m => m.mise > 0);
    if (!misesJouees.length) continue;

    let netTotal = 0;
    const morceaux = [];

    for (const m of misesJouees) {
      const tm = compter(m.cartes);
      const bjMoi = p.mains.length === 1 && estBlackjack(m.cartes);
      let texte = '', classe = '', delta = 0;

      if (tm > 21) {
        texte = 'dépasse 21, la banque encaisse ' + eur(m.mise);
        classe = 'perdu';
        delta = -m.mise;
      } else if (bjMoi && !bjBanque) {
        const g = sous(m.mise * 2.5);
        delta = g - m.mise;
        texte = 'blackjack, +' + eur(g - m.mise);
        classe = 'gagne';
      } else if (tb > 21) {
        const g = sous(m.mise * 2);
        delta = g - m.mise;
        texte = 'la banque saute, +' + eur(g - m.mise);
        classe = 'gagne';
      } else if (tm > tb) {
        const g = sous(m.mise * 2);
        delta = g - m.mise;
        texte = tm + ' contre ' + tb + ', +' + eur(g - m.mise);
        classe = 'gagne';
      } else if (tm < tb) {
        texte = tb + ' pour la banque, -' + eur(m.mise);
        classe = 'perdu';
        delta = -m.mise;
      } else {
        texte = 'égalité à ' + tm + ', mise rendue';
        classe = '';
        delta = 0;
      }

      m.resultat = { texte, classe };
      p.solde = sous(p.solde + m.mise + delta);
      netTotal += delta;
      morceaux.push(texte);
    }

    const classeGlobale = netTotal > 0 ? 'gagne' : (netTotal < 0 ? 'perdu' : '');
    const texteGlobal = misesJouees.length > 1
      ? morceaux.map((t, i) => 'Main ' + (i + 1) + ' : ' + t + '.').join(' ')
      : (morceaux[0] ? morceaux[0].charAt(0).toUpperCase() + morceaux[0].slice(1) + '.' : '');

    p.resultat = { texte: texteGlobal, classe: classeGlobale };
    majSoldeCompte(p);

    // on inscrit la manche au carnet du joueur
    if (p.type === 'humain' && p.jeton) {
      const c = comptes.get(p.jeton);
      if (c) {
        c.mains++;
        if (classeGlobale === 'gagne')      c.gagnees++;
        else if (classeGlobale === 'perdu') c.perdues++;
        Carnet.enregistrer(c);
      }
    }

    // Don Koala se moque, uniquement chez le joueur qui a perdu deux fois
    if (classeGlobale === 'perdu') {
      p.pertesDeSuite = (p.pertesDeSuite || 0) + 1;
      if (p.pertesDeSuite >= 2) { p.provocation = true; p.pertesDeSuite = 0; }
    } else if (classeGlobale === 'gagne') {
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
          if (p) p.mains[table.mainActive].etat = 'reste';
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
  const compte = comptes.get(jeton);

  const places = table.places.map((p, i) => {
    if (!p) return null;
    const estMoi = i === moiIndex;
    return {
      nom: p.nom,
      moi: estMoi,
      bot: p.type === 'bot',
      humain: p.type === 'humain',
      mains: p.mains.map(m => ({
        cartes: m.cartes, mise: m.mise, etat: m.etat,
        total: compter(m.cartes), resultat: m.resultat
      })),
      etat: p.etat,
      // le solde des autres n'est envoye que s'ils ont choisi de l'afficher
      solde: (estMoi || p.soldeVisible) ? p.solde : null,
      soldeVisible: !!p.soldeVisible
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

  const mainActiveMoi = moi ? moi.mains[table.mainActive] : null;

  return {
    version: table.version,
    table: table.id,
    nom: table.nom,
    skin: table.skin,
    phase: table.phase,
    secondes,
    indexActif: table.indexActif,
    mainActive: table.mainActive,
    cacheeRevelee: table.cacheeRevelee,
    banque,
    totalBanque: table.cacheeRevelee
      ? compter(table.banque)
      : (table.banque.length ? compter([table.banque[0]]) : 0),
    places,
    monIndex: moiIndex,
    monTour: moiIndex >= 0 && moiIndex === table.indexActif && table.phase === 'joueur',
    monSolde: moi ? moi.solde : (compte ? compte.solde : 0),
    monSoldeVisible: !!(moi && moi.soldeVisible),
    maMise: moi ? moi.mains.reduce((s, m) => s + m.mise, 0) : 0,
    peutDoubler: !!(mainActiveMoi && mainActiveMoi.cartes.length === 2 && moi.solde >= mainActiveMoi.mise),
    peutDiviser: !!(moi && moi.mains.length === 1 && mainActiveMoi &&
      mainActiveMoi.cartes.length === 2 &&
      mainActiveMoi.cartes[0].h === mainActiveMoi.cartes[1].h &&
      moi.solde >= mainActiveMoi.mise),
    monResultat: moi ? moi.resultat : null,
    provocation,
    message: table.message,
    assis: moiIndex >= 0,
    chat: table.chat.map(m => ({
      id: m.id, nom: m.nom, texte: m.texte, systeme: !!m.systeme, t: m.t || 0,
      moi: !!(m.jeton && m.jeton === jeton),
      cadeau: m.cadeau ? {
        de: m.cadeau.de, a: m.cadeau.a, montant: m.cadeau.montant,
        pourMoi: m.cadeau.aJeton === jeton,     // c'est moi qui reçois
        deMoi:   m.cadeau.deJeton === jeton     // c'est moi qui offre
      } : null
    }))
  };
}

function resumeSalon() {
  return tables.map(t => ({
    id: t.id,
    nom: t.nom,
    mini: t.mini,
    skin: t.skin,
    phase: t.phase,
    places: t.places.map(p => p ? { nom: p.nom, bot: p.type === 'bot' } : null),
    joueurs: t.places.filter(p => p && p.type === 'humain').length
  }));
}

/* ===================================================================
   ROULETTE — une seule table partagée, le serveur tient l'économie
   -------------------------------------------------------------------
   Ajout autonome : aucune fonction du blackjack ci-dessus n'est
   modifiée. La table de roulette vit dans son propre objet, avec son
   propre battement (setInterval séparé) et ses propres routes
   /api/roulette-*, pour ne prendre aucun risque avec le blackjack.
   =================================================================== */
const ZONES_ROULETTE = [{"id":"n0","type":"plein","nums":[0]},{"id":"n1","type":"plein","nums":[1]},{"id":"n2","type":"plein","nums":[2]},{"id":"n3","type":"plein","nums":[3]},{"id":"n4","type":"plein","nums":[4]},{"id":"n5","type":"plein","nums":[5]},{"id":"n6","type":"plein","nums":[6]},{"id":"n7","type":"plein","nums":[7]},{"id":"n8","type":"plein","nums":[8]},{"id":"n9","type":"plein","nums":[9]},{"id":"n10","type":"plein","nums":[10]},{"id":"n11","type":"plein","nums":[11]},{"id":"n12","type":"plein","nums":[12]},{"id":"n13","type":"plein","nums":[13]},{"id":"n14","type":"plein","nums":[14]},{"id":"n15","type":"plein","nums":[15]},{"id":"n16","type":"plein","nums":[16]},{"id":"n17","type":"plein","nums":[17]},{"id":"n18","type":"plein","nums":[18]},{"id":"n19","type":"plein","nums":[19]},{"id":"n20","type":"plein","nums":[20]},{"id":"n21","type":"plein","nums":[21]},{"id":"n22","type":"plein","nums":[22]},{"id":"n23","type":"plein","nums":[23]},{"id":"n24","type":"plein","nums":[24]},{"id":"n25","type":"plein","nums":[25]},{"id":"n26","type":"plein","nums":[26]},{"id":"n27","type":"plein","nums":[27]},{"id":"n28","type":"plein","nums":[28]},{"id":"n29","type":"plein","nums":[29]},{"id":"n30","type":"plein","nums":[30]},{"id":"n31","type":"plein","nums":[31]},{"id":"n32","type":"plein","nums":[32]},{"id":"n33","type":"plein","nums":[33]},{"id":"n34","type":"plein","nums":[34]},{"id":"n35","type":"plein","nums":[35]},{"id":"n36","type":"plein","nums":[36]},{"id":"col0","type":"colonne","nums":[3,6,9,12,15,18,21,24,27,30,33,36]},{"id":"col1","type":"colonne","nums":[2,5,8,11,14,17,20,23,26,29,32,35]},{"id":"col2","type":"colonne","nums":[1,4,7,10,13,16,19,22,25,28,31,34]},{"id":"douz0","type":"douzaine","nums":[1,2,3,4,5,6,7,8,9,10,11,12]},{"id":"douz1","type":"douzaine","nums":[13,14,15,16,17,18,19,20,21,22,23,24]},{"id":"douz2","type":"douzaine","nums":[25,26,27,28,29,30,31,32,33,34,35,36]},{"id":"manque","type":"manque","nums":[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18]},{"id":"pair","type":"pair","nums":[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36]},{"id":"rouge","type":"rouge","nums":[1,3,5,7,9,12,14,16,18,19,21,23,25,27,30,32,34,36]},{"id":"noir","type":"noir","nums":[2,4,6,8,10,11,13,15,17,20,22,24,26,28,29,31,33,35]},{"id":"impair","type":"impair","nums":[1,3,5,7,9,11,13,15,17,19,21,23,25,27,29,31,33,35]},{"id":"passe","type":"passe","nums":[19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]}];

const SEQUENCE_ROULETTE = [0,32,15,19,4,21,2,25,17,34,6,27,13,36,11,30,8,23,10,5,24,16,33,1,20,14,31,9,22,18,29,7,28,12,35,3,26];
const ROUGES_ROULETTE   = [1,3,5,7,9,12,14,16,18,19,21,23,25,27,30,32,34,36];
function couleurRoulette(n) { if (n === 0) return 'vert'; return ROUGES_ROULETTE.indexOf(n) >= 0 ? 'rouge' : 'noir'; }
function trouverZoneRoulette(id) { return ZONES_ROULETTE.find(z => z.id === id) || null; }
function multiplicateurZoneRoulette(type) {
  if (type === 'plein') return 36;
  if (type === 'colonne' || type === 'douzaine') return 3;
  return 2; // rouge, noir, pair, impair, manque, passe
}

const DUREE_MISE_ROULETTE       = 15000;  // temps pour miser
const DUREE_LANCEMENT_ROULETTE  = 6600;   // 2000ms tapis + 4600ms cinema, comme le prototype
const DUREE_RESULTAT_ROULETTE   = 5000;   // affichage du resultat avant la manche suivante
const NB_PLACES_ROULETTE        = 7;

const tableRoulette = {
  id: 'roulette',
  nom: 'Roulette Messina',
  places: new Array(NB_PLACES_ROULETTE).fill(null),
  phase: 'mise',           // 'mise' | 'lancement' | 'resultat'
  echeance: Date.now() + DUREE_MISE_ROULETTE,
  numeroGagnant: null,
  historique: [],
  version: 1
};

function toucheRoulette() { tableRoulette.version++; }

function rembourserMisesRoulette(p) {
  if (!p) return;
  const c = comptes.get(p.jeton);
  if (!c) return;
  let total = 0;
  Object.keys(p.mises).forEach(id => { total += p.mises[id]; });
  if (total > 0) { c.solde = sous(c.solde + total); }
  p.mises = {};
}

function nouvelleMancheRoulette() {
  tableRoulette.phase = 'mise';
  tableRoulette.echeance = Date.now() + DUREE_MISE_ROULETTE;
  tableRoulette.numeroGagnant = null;
  tableRoulette.places.forEach(p => { if (p) { p.mises = {}; p.dernierGain = 0; p.derniereMiseTotale = 0; } });
  toucheRoulette();
}

function demarrerLancementRoulette() {
  const numero = SEQUENCE_ROULETTE[crypto.randomInt(SEQUENCE_ROULETTE.length)];
  const couleur = couleurRoulette(numero);
  tableRoulette.numeroGagnant = numero;

  tableRoulette.places.forEach(p => {
    if (!p) return;
    const c = comptes.get(p.jeton);
    let miseTotale = 0, gains = 0;
    Object.keys(p.mises).forEach(id => {
      const zone = trouverZoneRoulette(id);
      if (!zone) return;
      miseTotale += p.mises[id];
      if (zone.nums.indexOf(numero) >= 0) {
        gains = sous(gains + sous(p.mises[id] * multiplicateurZoneRoulette(zone.type)));
      }
    });
    if (c) {
      if (gains > 0) c.solde = sous(c.solde + gains);
      c.roulettes = (c.roulettes | 0) + 1;
      Carnet.enregistrer(c);
    }
    p.dernierGain = gains;
    p.derniereMiseTotale = miseTotale;
    p.mises = {};
  });

  tableRoulette.historique.unshift({ n: numero, c: couleur });
  tableRoulette.historique = tableRoulette.historique.slice(0, 5);

  tableRoulette.phase = 'lancement';
  tableRoulette.echeance = Date.now() + DUREE_LANCEMENT_ROULETTE;
  toucheRoulette();
}

function battementRoulette() {
  const now = Date.now();
  const t = tableRoulette;

  let depart = false;
  t.places.forEach((p, i) => {
    if (!p) return;
    const c = comptes.get(p.jeton);
    if (!c || now - c.vu > ABSENCE_MAX) {
      rembourserMisesRoulette(p);
      if (c) c.tableRoulette = false;
      t.places[i] = null;
      depart = true;
    }
  });
  if (depart) toucheRoulette();

  switch (t.phase) {
    case 'mise':
      if (now >= t.echeance) demarrerLancementRoulette();
      break;
    case 'lancement':
      if (now >= t.echeance) {
        t.phase = 'resultat';
        t.echeance = now + DUREE_RESULTAT_ROULETTE;
        toucheRoulette();
      }
      break;
    case 'resultat':
      if (now >= t.echeance) nouvelleMancheRoulette();
      break;
  }
}
setInterval(battementRoulette, 200);

function etatRoulette(jeton) {
  const t = tableRoulette;
  const moiIndex = t.places.findIndex(p => p && p.jeton === jeton);
  const moi = moiIndex >= 0 ? t.places[moiIndex] : null;
  const now = Date.now();
  const c = comptes.get(jeton);

  let secondes = 0;
  if (t.phase === 'mise') secondes = Math.max(0, Math.ceil((t.echeance - now) / 1000));

  return {
    assis: moiIndex >= 0,
    version: t.version,
    phase: t.phase,
    secondes,
    echeance: t.echeance,
    dureeLancement: DUREE_LANCEMENT_ROULETTE,
    dureeResultat: DUREE_RESULTAT_ROULETTE,
    numeroGagnant: (t.phase === 'lancement' || t.phase === 'resultat') ? t.numeroGagnant : null,
    historique: t.historique,
    places: t.places.map((p, i) => p ? { nom: p.nom, moi: i === moiIndex } : null),
    mesMises: moi ? moi.mises : {},
    dernierGain: moi ? (moi.dernierGain || 0) : 0,
    derniereMiseTotale: moi ? (moi.derniereMiseTotale || 0) : 0,
    solde: c ? c.solde : 0
  };
}

function resumeRoulette() {
  return {
    id: tableRoulette.id,
    nom: tableRoulette.nom,
    phase: tableRoulette.phase,
    joueurs: tableRoulette.places.filter(p => p).length,
    places: NB_PLACES_ROULETTE,
    dernier: tableRoulette.historique.length ? tableRoulette.historique[0] : null
  };
}

function quitterTableRoulette(compte) {
  const i = tableRoulette.places.findIndex(p => p && p.jeton === compte.jetonRef);
  if (i >= 0) {
    rembourserMisesRoulette(tableRoulette.places[i]);
    tableRoulette.places[i] = null;
    toucheRoulette();
  }
  compte.tableRoulette = false;
}

/* ===================================================================
   LE PERIPH — depart d'une course, en solo comme en multijoueur
   -------------------------------------------------------------------
   Factorise pour que la route /api/periph-demarrer (solo, inchangee)
   et le demarrage d'un groupe multijoueur debitent la mise et ouvrent
   la course exactement de la meme facon.
   =================================================================== */
function demarrerCourseInterne(compte, mise, voitureDemandee) {
  const voiture = (Number(voitureDemandee) | 0) === VOITURE_PREMIUM_INDICE && compte.voiturePremium
    ? VOITURE_PREMIUM_INDICE : bornerVoitureNormale(voitureDemandee);

  compte.solde  = sous(compte.solde - mise);
  compte.periph = { mise: mise, palier: 0, depart: Date.now(), voiture: voiture };
  compte.periphs = (compte.periphs | 0) + 1;

  const info = siegeDe(compte);
  if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
  Carnet.enregistrer(compte);

  return voiture;
}

/* ===================================================================
   LE PERIPH EN MULTIJOUEUR — file d'attente et groupes de course
   =================================================================== */
const filePeriphMulti = [];             // {jeton, pseudo, mise, voiture, couleur, rejointLe}
let   groupeEnFormationPeriph = null;   // {echeance, jetons:[...]}
const groupesCoursePeriph = new Map();  // id -> {creeLe, membres:{jeton:{pseudo,couleur,palier,fraction,statut,maj}}}
let   compteurGroupePeriph = 1;

function retirerDeLaFilePeriph(jeton) {
  const i = filePeriphMulti.findIndex(e => e.jeton === jeton);
  if (i >= 0) filePeriphMulti.splice(i, 1);
}

function majGroupeCoursePeriph(compte, patch) {
  if (!compte.periphMulti) return;
  const g = groupesCoursePeriph.get(compte.periphMulti.groupeId);
  if (g && g.membres[compte.jetonRef]) Object.assign(g.membres[compte.jetonRef], patch, { maj: Date.now() });
}

function formerGroupePeriph() {
  if (groupeEnFormationPeriph) return;
  if (filePeriphMulti.length < 2) return;
  const membres = filePeriphMulti.slice(0, 4);
  const prises = [];
  membres.forEach(e => {
    let c = bornerVoitureNormale(e.couleur);
    if (prises.indexOf(c) >= 0) {
      let libre = 0;
      while (prises.indexOf(libre) >= 0 && libre < 4) libre++;
      c = libre < 4 ? libre : 0;
    }
    prises.push(c);
    e.couleurAffectee = c;
  });
  groupeEnFormationPeriph = {
    echeance: Date.now() + DUREE_ATTENTE_PERIPH_MULTI,
    jetons: membres.map(e => e.jeton)
  };
}

function demarrerCoursePeriphMulti(jetons) {
  const id = 'g' + (compteurGroupePeriph++);
  const membres = {};
  jetons.forEach(j => {
    const entree = filePeriphMulti.find(e => e.jeton === j);
    const compte = comptes.get(j);
    retirerDeLaFilePeriph(j);
    if (!entree || !compte) return;
    if (entree.mise > compte.solde + 1e-9) {
      compte.periphMultiErreur = 'Solde insuffisant : la course a démarré sans vous.';
      return;
    }
    const voiture = demarrerCourseInterne(compte, entree.mise, entree.voiture);
    compte.periphMulti = { groupeId: id, couleur: entree.couleurAffectee };
    membres[j] = {
      pseudo: compte.pseudo, couleur: entree.couleurAffectee,
      palier: 0, fraction: 0, statut: 'course', maj: Date.now(),
      voiture: voiture
    };
  });
  if (Object.keys(membres).length) groupesCoursePeriph.set(id, { creeLe: Date.now(), membres });
}

function battementPeriphMulti() {
  const now = Date.now();

  // on retire les joueurs qui ne donnent plus de nouvelles
  for (let i = filePeriphMulti.length - 1; i >= 0; i--) {
    const e = filePeriphMulti[i];
    const c = comptes.get(e.jeton);
    if (!c || now - c.vu > ABSENCE_MAX) filePeriphMulti.splice(i, 1);
  }

  if (groupeEnFormationPeriph) {
    const presents = groupeEnFormationPeriph.jetons.filter(j => filePeriphMulti.some(e => e.jeton === j));
    if (presents.length < 2) {
      groupeEnFormationPeriph = null;                 // annule : personne n'est debite
    } else if (now >= groupeEnFormationPeriph.echeance) {
      demarrerCoursePeriphMulti(presents);
      groupeEnFormationPeriph = null;
    }
  } else {
    formerGroupePeriph();
  }

  // les groupes de course perimes (course finie depuis un moment, ou trop vieille) sont oublies
  groupesCoursePeriph.forEach((g, id) => {
    const actif = Object.values(g.membres).some(m => m.statut === 'course');
    if ((!actif && now - g.creeLe > 15000) || now - g.creeLe > EXPIRATION_COURSE_MULTI) {
      groupesCoursePeriph.delete(id);
    }
  });
}
setInterval(battementPeriphMulti, 200);

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

// --- pour le code "RS6" : la liste de tous les comptes, avec leur presence
// reelle si une session est ouverte sur ce serveur, sinon la derniere fois
// vue selon l'index (voir Carnet.indexerJoueur). Les plus recemment vus
// d'abord.
function listeJoueursAvecPresence(liste) {
  const maintenant = Date.now();
  const joueurs = liste.map(j => {
    let vuLe = j.vuLe || null, enLigne = false;
    for (const c of comptes.values()) {
      if (c.pseudoBas === j.pseudoBas) {
        vuLe = new Date(c.vu).toISOString();
        enLigne = (maintenant - c.vu) < ABSENCE_MAX;
        break;
      }
    }
    return { pseudo: j.pseudo, creeLe: j.creeLe || null, vuLe: vuLe, enLigne: enLigne };
  });
  joueurs.sort((a, b) => new Date(b.vuLe || 0) - new Date(a.vuLe || 0));
  return joueurs;
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
        voiturePremium: false, codesUtilises: [], tower: null, tours: 0
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
      return repondre(res, 200, { tables: resumeSalon(), roulette: resumeRoulette(), solde: compte.solde });
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
        mains: [neuveMain(0)],
        etat: (table.phase === 'mise' || table.phase === 'attente') ? 'attente' : 'spectateur',
        solde: compte.solde, resultat: null, pertesDeSuite: 0, provocation: false,
        soldeVisible: !!compte.soldeVisible
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

    /* ================= ROULETTE ================= */

    // --- s'asseoir a la table de roulette ---
    if (route === '/api/roulette-asseoir' && req.method === 'POST') {
      // deja assis : on renvoie simplement l'etat
      let i = tableRoulette.places.findIndex(p => p && p.jeton === compte.jetonRef);
      if (i < 0) {
        i = tableRoulette.places.findIndex(p => !p);
        if (i < 0) return repondre(res, 409, { erreur: 'table complete' });
        tableRoulette.places[i] = { jeton: compte.jetonRef, nom: compte.pseudo, mises: {}, dernierGain: 0, derniereMiseTotale: 0 };
        compte.tableRoulette = true;
        toucheRoulette();
      }
      return repondre(res, 200, etatRoulette(compte.jetonRef));
    }

    // --- quitter la table de roulette ---
    if (route === '/api/roulette-quitter' && req.method === 'POST') {
      quitterTableRoulette(compte);
      return repondre(res, 200, { ok: true, solde: compte.solde });
    }

    // --- etat de la table de roulette (appele en boucle) ---
    if (route === '/api/roulette-etat') {
      return repondre(res, 200, etatRoulette(compte.jetonRef));
    }

    // --- placer une mise sur une zone ---
    if (route === '/api/roulette-miser' && req.method === 'POST') {
      const p = tableRoulette.places.find(x => x && x.jeton === compte.jetonRef);
      if (!p) return repondre(res, 409, { erreur: 'pas a table' });
      if (tableRoulette.phase !== 'mise') return repondre(res, 409, { erreur: 'trop tard' });

      const zone = trouverZoneRoulette(String(body.zone || ''));
      if (!zone) return repondre(res, 400, { erreur: 'zone inconnue' });

      let v = Number(body.montant);
      if (!isFinite(v) || v < 0.01) return repondre(res, 400, { erreur: 'mise trop faible' });
      v = sous(v);
      if (v > compte.solde + 1e-9) return repondre(res, 400, { erreur: 'solde insuffisant' });

      compte.solde = sous(compte.solde - v);
      p.mises[zone.id] = sous((p.mises[zone.id] || 0) + v);
      toucheRoulette();
      return repondre(res, 200, etatRoulette(compte.jetonRef));
    }

    // --- effacer mes mises de la manche en cours (remboursement) ---
    if (route === '/api/roulette-effacer' && req.method === 'POST') {
      const p = tableRoulette.places.find(x => x && x.jeton === compte.jetonRef);
      if (!p) return repondre(res, 409, { erreur: 'pas a table' });
      if (tableRoulette.phase !== 'mise') return repondre(res, 409, { erreur: 'trop tard' });
      rembourserMisesRoulette(p);
      toucheRoulette();
      return repondre(res, 200, etatRoulette(compte.jetonRef));
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

      p.mains[0].mise = v;
      p.solde = sous(p.solde - v);
      majSoldeCompte(p);
      touche(table);
      return repondre(res, 200, etatPour(table, compte.jetonRef));
    }

    // --- carte / rester / doubler / diviser (split) ---
    if (route === '/api/action' && req.method === 'POST') {
      const info = siegeDe(compte);
      if (!info || !info.p) return repondre(res, 409, { erreur: 'pas a table' });
      const { table, p } = info;
      const monIndex = table.places.indexOf(p);
      if (table.phase !== 'joueur' || table.indexActif !== monIndex) {
        return repondre(res, 409, { erreur: 'pas votre tour' });
      }

      const action = String(body.action || '');
      const m = p.mains[table.mainActive];

      if (action === 'carte') {
        m.cartes.push(tirer(table));
        const t = compter(m.cartes);
        if (t > 21)       { m.etat = 'saute'; touche(table); tourSuivant(table); }
        else if (t === 21){ m.etat = 'reste'; touche(table); tourSuivant(table); }
        else              { table.echeance = Date.now() + DUREE_TOUR; touche(table); }

      } else if (action === 'rester') {
        m.etat = 'reste';
        touche(table);
        tourSuivant(table);

      } else if (action === 'doubler') {
        if (m.cartes.length !== 2 || p.solde < m.mise) {
          return repondre(res, 400, { erreur: 'doublement impossible' });
        }
        p.solde = sous(p.solde - m.mise);
        m.mise  = sous(m.mise * 2);
        majSoldeCompte(p);
        m.cartes.push(tirer(table));
        m.etat = compter(m.cartes) > 21 ? 'saute' : 'reste';
        touche(table);
        tourSuivant(table);

      } else if (action === 'diviser') {
        if (p.mains.length !== 1 || m.cartes.length !== 2 ||
            m.cartes[0].h !== m.cartes[1].h || p.solde < m.mise) {
          return repondre(res, 400, { erreur: 'partage impossible' });
        }
        p.solde = sous(p.solde - m.mise);
        majSoldeCompte(p);
        const secondeCarte = m.cartes.pop();
        p.mains.push({ cartes: [secondeCarte], mise: m.mise, etat: 'attente', resultat: null });
        m.cartes.push(tirer(table));
        p.mains[1].cartes.push(tirer(table));
        if (compter(m.cartes) === 21) m.etat = 'reste';
        table.echeance = Date.now() + DUREE_TOUR;
        touche(table);

      } else {
        return repondre(res, 400, { erreur: 'action inconnue' });
      }

      return repondre(res, 200, etatPour(table, compte.jetonRef));
    }

    // --- offrir de l'argent a un joueur assis a la meme table ---
    if (route === '/api/table-offrir' && req.method === 'POST') {
      const info = siegeDe(compte);
      if (!info || !info.p) return repondre(res, 409, { erreur: 'pas a table' });
      const { table, p } = info;

      const cible = table.places[Number(body.place)];
      if (!cible || cible.type !== 'humain' || cible === p) {
        return repondre(res, 404, { erreur: 'destinataire introuvable' });
      }
      let v = Number(body.montant);
      if (!isFinite(v) || v < 0.01) return repondre(res, 400, { erreur: 'montant trop faible' });
      v = sous(v);
      if (v > p.solde + 1e-9) return repondre(res, 400, { erreur: 'solde insuffisant' });

      p.solde = sous(p.solde - v);
      cible.solde = sous(cible.solde + v);
      majSoldeCompte(p);
      majSoldeCompte(cible);
      // le don est inscrit dans le chat de la table ; le champ "cadeau"
      // permet au destinataire (et a lui seul) d'afficher une notification
      table.chat.push({
        id: ++table.chatId, systeme: true,
        texte: p.nom + ' offre ' + eur(v) + ' à ' + cible.nom + '.', t: Date.now(),
        cadeau: { de: p.nom, a: cible.nom, montant: v, deJeton: p.jeton, aJeton: cible.jeton }
      });
      if (table.chat.length > CHAT_MAX) table.chat.splice(0, table.chat.length - CHAT_MAX);
      touche(table);
      return repondre(res, 200, etatPour(table, compte.jetonRef));
    }

    // --- afficher ou masquer son solde aux autres joueurs ---
    if (route === '/api/table-visibilite' && req.method === 'POST') {
      compte.soldeVisible = !!body.visible;
      const info = siegeDe(compte);
      if (info && info.p) {
        info.p.soldeVisible = compte.soldeVisible;
        touche(info.table);
        return repondre(res, 200, etatPour(info.table, compte.jetonRef));
      }
      return repondre(res, 200, { ok: true, soldeVisible: compte.soldeVisible });
    }

    // --- chat de table (ephemere : voir cote client pour l'affichage) ---
    if (route === '/api/table-chat' && req.method === 'POST') {
      const info = siegeDe(compte);
      if (!info || !info.p) return repondre(res, 409, { erreur: 'pas a table' });
      const { table, p } = info;
      const texte = String(body.texte || '').trim().slice(0, 240);
      if (!texte) return repondre(res, 400, { erreur: 'message vide' });

      table.chat.push({ id: ++table.chatId, nom: p.nom, moi: false, jeton: p.jeton, texte, t: Date.now() });
      if (table.chat.length > CHAT_MAX) table.chat.splice(0, table.chat.length - CHAT_MAX);
      touche(table);
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
      // une course abandonnee en route est simplement perdue : on repart proprement
      const voiture = demarrerCourseInterne(compte, mise, body.voiture);

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
        majGroupeCoursePeriph(compte, { statut: 'crash' });
        compte.periphMulti = null;
        Carnet.enregistrer(compte);
        return repondre(res, 400, { erreur: 'Course invalide.' });
      }

      course.palier  = suivant;
      compte.portes  = (compte.portes | 0) + 1;
      const gain     = sous(course.mise * ECHELLE_PERIPH[suivant - 1]);
      const fini     = suivant >= ECHELLE_PERIPH.length;

      // pour l'affichage de la voiture des autres joueurs reels (multijoueur uniquement)
      majGroupeCoursePeriph(compte, { palier: suivant, fraction: 0, statut: fini ? 'arrive' : 'course' });

      if (fini) {                                   // Saint-Denis : on encaisse d'office
        compte.solde  = sous(compte.solde + gain);
        compte.periph = null;
        compte.periphMulti = null;
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
      majGroupeCoursePeriph(compte, { statut: 'encaisse' });
      compte.periphMulti = null;

      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
      Carnet.enregistrer(compte);

      return repondre(res, 200, { ok: true, gain: gain, solde: compte.solde });
    }

    // --- la voiture est detruite, ou on s'est fait doubler ---
    if (route === '/api/periph-perdu' && req.method === 'POST') {
      compte.periph = null;
      majGroupeCoursePeriph(compte, { statut: 'crash' });
      compte.periphMulti = null;
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, solde: compte.solde });
    }

    /* ===============================================================
       LE PERIPH EN MULTIJOUEUR
       ---------------------------------------------------------------
       Une vraie file d'attente : le depart n'a lieu que si un deuxieme
       joueur reel rejoint. Le gain/la perte de chacun reste toujours
       gouverne par les routes ci-dessus, inchangees.
       =============================================================== */

    // --- on rejoint la file d'attente ---
    if (route === '/api/periph-multi-rejoindre' && req.method === 'POST') {
      if (compte.periph) return repondre(res, 409, { erreur: 'Terminez votre course en cours.' });
      if (compte.periphMulti) return repondre(res, 409, { erreur: 'Vous êtes déjà en course.' });
      if (filePeriphMulti.some(e => e.jeton === compte.jetonRef)) {
        return repondre(res, 200, { ok: true });
      }
      const mise = sous(Number(body.mise) || 0);
      if (!(mise >= MISE_MINI_PERIPH)) return repondre(res, 400, { erreur: 'Mise minimum : 0,10 €.' });
      if (mise > MISE_MAXI_PERIPH) return repondre(res, 400, { erreur: 'Mise maximum : 100,00 €.' });
      if (mise > compte.solde) return repondre(res, 400, { erreur: 'Solde insuffisant.' });

      const voitureDemandee = (Number(body.voiture) | 0) === VOITURE_PREMIUM_INDICE && compte.voiturePremium
        ? VOITURE_PREMIUM_INDICE : bornerVoitureNormale(body.voiture);
      const couleur = bornerVoitureNormale(body.couleur);

      compte.periphMultiErreur = null;
      filePeriphMulti.push({
        jeton: compte.jetonRef, pseudo: compte.pseudo, mise: mise,
        voiture: voitureDemandee, couleur: couleur, rejointLe: Date.now()
      });
      return repondre(res, 200, { ok: true });
    }

    // --- on quitte la file d'attente (bouton ou changement d'avis) ---
    if (route === '/api/periph-multi-quitter' && req.method === 'POST') {
      retirerDeLaFilePeriph(compte.jetonRef);
      return repondre(res, 200, { ok: true });
    }

    // --- etat de la file / du compte a rebours (appele en boucle) ---
    if (route === '/api/periph-multi-etat') {
      if (compte.periphMulti && groupesCoursePeriph.has(compte.periphMulti.groupeId)) {
        return repondre(res, 200, {
          statut: 'parti',
          groupeId: compte.periphMulti.groupeId,
          couleur: compte.periphMulti.couleur,
          voiture: compte.periph ? compte.periph.voiture : compte.periphMulti.couleur,
          solde: compte.solde
        });
      }
      const enFile = filePeriphMulti.find(e => e.jeton === compte.jetonRef);
      if (enFile) {
        const dansGroupe = groupeEnFormationPeriph && groupeEnFormationPeriph.jetons.indexOf(compte.jetonRef) >= 0;
        if (dansGroupe) {
          const secondes = Math.max(0, Math.ceil((groupeEnFormationPeriph.echeance - Date.now()) / 1000));
          return repondre(res, 200, {
            statut: 'compteADebours', secondes: secondes,
            effectif: groupeEnFormationPeriph.jetons.length
          });
        }
        return repondre(res, 200, { statut: 'attente' });
      }
      if (compte.periphMultiErreur) {
        const erreur = compte.periphMultiErreur;
        compte.periphMultiErreur = null;
        return repondre(res, 200, { statut: 'erreur', erreur: erreur });
      }
      return repondre(res, 200, { statut: 'aucune' });
    }

    // --- on annonce sa progression approximative, pour dessiner sa voiture chez les autres ---
    if (route === '/api/periph-multi-progres' && req.method === 'POST') {
      if (!compte.periphMulti) return repondre(res, 409, { erreur: 'pas en course' });
      const g = groupesCoursePeriph.get(compte.periphMulti.groupeId);
      if (g && g.membres[compte.jetonRef] && g.membres[compte.jetonRef].statut === 'course') {
        g.membres[compte.jetonRef].fraction = Math.max(0, Math.min(1, Number(body.fraction) || 0));
        g.membres[compte.jetonRef].x = Math.max(-7, Math.min(7, Number(body.x) || 0));
        g.membres[compte.jetonRef].maj = Date.now();
      }
      return repondre(res, 200, { ok: true });
    }

    // --- on recupere la progression des autres joueurs reels de la course ---
    if (route === '/api/periph-multi-course') {
      if (!compte.periphMulti) return repondre(res, 200, { membres: [] });
      const g = groupesCoursePeriph.get(compte.periphMulti.groupeId);
      if (!g) return repondre(res, 200, { membres: [] });
      const membres = Object.keys(g.membres)
        .filter(j => j !== compte.jetonRef)
        .map(j => {
          const m = g.membres[j];
          return { pseudo: m.pseudo, couleur: m.couleur, voiture: m.voiture, palier: m.palier, fraction: m.fraction, x: m.x || 0, maj: m.maj || 0, statut: m.statut };
        });
      return repondre(res, 200, { membres: membres });
    }

    /* ===============================================================
       TOWER RUSH
       ---------------------------------------------------------------
       Le seul chiffre que la page choisit vraiment, c'est le moment ou
       elle demande le lacher. Tout le reste (l'instant exact ou ca en
       etait dans le balancement, la precision qui en decoule, le
       multiplicateur tire, le risque d'effondrement) est recalcule ici
       a partir de l'heure d'arrivee de la requete. Personne ne peut
       forcer un bon multiplicateur en trafiquant la page.
       =============================================================== */

    // --- on pose sa mise, le premier etage commence a se balancer ---
    if (route === '/api/tower-demarrer' && req.method === 'POST') {
      if (compte.tower) return repondre(res, 409, { erreur: 'Une tour est déjà en cours.' });
      const mise = sous(Number(body.mise) || 0);
      if (!(mise >= MISE_MINI_TOWER)) return repondre(res, 400, { erreur: 'Mise minimum : 0,10 €.' });
      if (mise > MISE_MAXI_TOWER)     return repondre(res, 400, { erreur: 'Mise maximum : 500 €.' });
      if (mise > compte.solde)        return repondre(res, 400, { erreur: 'Solde insuffisant.' });

      compte.solde = sous(compte.solde - mise);
      compte.tower = {
        mise: mise, floors: [], leanSum: 0, visOffset: 0, frozenLeft: 0,
        totalMult: 1, swingStart: Date.now()
      };
      compte.tours = (compte.tours | 0) + 1;

      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
      Carnet.enregistrer(compte);

      return repondre(res, 200, {
        ok: true, mise: mise, solde: compte.solde,
        swingStart: compte.tower.swingStart, amp: towerAmpFor(0), period: towerPeriodFor(0)
      });
    }

    // --- on lache : le serveur recalcule seul ou en etait le balancement ---
    if (route === '/api/tower-lacher' && req.method === 'POST') {
      const tour = compte.tower;
      if (!tour) return repondre(res, 409, { erreur: 'Aucune tour en cours.' });

      const n = tour.floors.length;
      const amp = towerAmpFor(n), period = towerPeriodFor(n);
      const ecoule = Math.max(0, Date.now() - tour.swingStart) / 1000;
      let angle = amp * Math.sin(2 * Math.PI * ecoule / period);
      const etaitGele = tour.frozenLeft > 0;
      if (etaitGele) angle *= 0.2;

      const errRatio = Math.abs(angle) / amp;
      const safeT = 0.44, missT = Math.max(0.6, 0.92 - n * 0.016);
      const edgeT = towerClamp((errRatio - safeT) / Math.max(0.001, missT - safeT), 0, 1);
      const missChance = etaitGele ? 0 : edgeT * edgeT;
      const rate = Math.random() < missChance;

      if (rate) {
        const perdu = tour.mise;
        compte.tower = null;
        Carnet.enregistrer(compte);
        return repondre(res, 200, {
          ok: true, rate: true, angle: angle, perdu: perdu, solde: compte.solde
        });
      }

      const facteur = etaitGele ? towerRand(1.4, 2.0) : towerRollFactor(n, errRatio);
      if (etaitGele) tour.frozenLeft--;
      const parfait = !etaitGele && errRatio < 0.1 && facteur >= 1.6;

      tour.totalMult = tour.totalMult * facteur; // pas d'arrondi ici : seul le gain final (mise x totalMult) est arrondi
      const nouveauLean = tour.leanSum + angle * 0.58;
      const glisse = (tour.frozenLeft <= 0) && Math.abs(nouveauLean) > 58;
      tour.leanSum = nouveauLean;
      tour.visOffset = towerClamp(tour.visOffset + towerClamp(angle * 0.34, -22, 22), -74, 74);
      tour.floors.push({ mult: facteur, lean: tour.visOffset });

      if (glisse) {
        const perdu = tour.mise;
        const totalAvantChute = tour.totalMult;
        compte.tower = null;
        Carnet.enregistrer(compte);
        return repondre(res, 200, {
          ok: true, rate: false, glisse: true, facteur: facteur, lean: tour.visOffset,
          totalMult: totalAvantChute, perdu: perdu, solde: compte.solde
        });
      }

      // etage gele une fois toutes les ~14 etages en moyenne, pour souffler un peu
      if (!etaitGele && Math.random() < 0.07) tour.frozenLeft = 2 + (Math.random() < 0.5 ? 0 : 1);

      tour.swingStart = Date.now();
      Carnet.enregistrer(compte);
      return repondre(res, 200, {
        ok: true, rate: false, glisse: false, facteur: facteur, parfait: parfait,
        lean: tour.visOffset, totalMult: tour.totalMult, solde: compte.solde,
        gele: tour.frozenLeft > 0,
        swingStart: tour.swingStart, amp: towerAmpFor(n + 1), period: towerPeriodFor(n + 1)
      });
    }

    // --- on quitte en cours de tour : la mise reste perdue, comme pour le periph ---
    if (route === '/api/tower-abandonner' && req.method === 'POST') {
      compte.tower = null;
      return repondre(res, 200, { ok: true });
    }

    // --- on encaisse ---
    if (route === '/api/tower-encaisser' && req.method === 'POST') {
      const tour = compte.tower;
      if (!tour) return repondre(res, 409, { erreur: 'Aucune tour en cours.' });
      if (tour.floors.length < 1) return repondre(res, 400, { erreur: 'Posez au moins un étage avant d’encaisser.' });

      const gain = sous(tour.mise * tour.totalMult);
      compte.solde = sous(compte.solde + gain);
      compte.tower = null;

      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
      Carnet.enregistrer(compte);

      return repondre(res, 200, { ok: true, gain: gain, solde: compte.solde });
    }

    /* ===============================================================
       CODES DU PROFIL
       ---------------------------------------------------------------
       "50€" credite 50,00 € une seule fois par compte. "RS6" ne touche
       pas au solde : il revele la liste de tous les comptes deja crees
       (pseudo, creation, derniere fois vu), pour le proprietaire du
       site. On accepte l'espace, le signe € et "eur"/"euros" en trop,
       parce que c'est malcommode a taper sur un telephone.
       =============================================================== */
    if (route === '/api/code' && req.method === 'POST') {
      let normalise = String(body.code || '').trim().toLowerCase()
        .replace(/\s+/g, '').replace(/€/g, '')
        .replace(/(euros|euro|eur)$/, '');

      if (normalise === '50') {
        if (!Array.isArray(compte.codesUtilises)) compte.codesUtilises = [];
        if (compte.codesUtilises.indexOf('50EUROS') >= 0) {
          return repondre(res, 409, { erreur: 'Ce code a déjà été utilisé.' });
        }
        compte.codesUtilises.push('50EUROS');
        compte.solde = sous(compte.solde + 50);
        const info = siegeDe(compte);
        if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, genre: 'credit', solde: compte.solde });
      }

      if (normalise === 'rs6') {
        const liste = await Carnet.listerJoueurs();
        return repondre(res, 200, { ok: true, genre: 'liste', joueurs: listeJoueursAvecPresence(liste) });
      }

      return repondre(res, 400, { erreur: 'Code invalide.' });
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
        roulettes: compte.roulettes | 0,
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
    if (c.pseudoBas === fiche.pseudoBas) {
      quitterTable(c); quitterTableRoulette(c); retirerDeLaFilePeriph(c.jetonRef);
      comptes.delete(j);
    }
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
    roulettes: fiche.roulettes | 0,
    buts:      fiche.buts     | 0,
    defaitesPenalty: fiche.defaitesPenalty | 0,
    perso:     fiche.perso || null,
    voiturePremium: !!fiche.voiturePremium,
    codesUtilises: Array.isArray(fiche.codesUtilises) ? fiche.codesUtilises.slice() : [],
    penalty: null,                       // aucune serie de penaltys en cours
    periph:  null,                       // aucune course de periph en cours
    periphMulti: null,                   // pas dans un groupe de course multijoueur
    table: null, siege: -1, tableRoulette: false, vu: Date.now()
  };
  comptes.set(jeton, compte);
  Carnet.indexerJoueur(fiche.pseudoBas, fiche.pseudo);

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
