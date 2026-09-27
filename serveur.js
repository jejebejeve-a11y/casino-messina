'use strict';
/* ===================================================================
   CASINO MESSINA - serveur de jeu
   -------------------------------------------------------------------
   Aucune bibliotheque a installer : uniquement Node.
   Le serveur tient les cartes, les tours et le chronometre.
   Regle absolue : chaque phase a une duree maximum. Quand le temps
   est ecoule, la partie avance, que les joueurs aient repondu ou non.
   Personne ne peut bloquer personne.
   =================================================================== */

const http       = require('http');
const fs         = require('fs');
const path       = require('path');
const crypto     = require('crypto');
const https      = require('https');
const nodemailer = require('nodemailer');

const PORT    = process.env.PORT || 3000;
const DOSSIER = __dirname;

/* ---------- durees, en millisecondes ---------- */
const DUREE_MISE      = 12000;  // temps pour miser
const DUREE_TOUR      = 15000;  // temps pour jouer son tour
const DUREE_RESULTAT  = 6000;   // affichage du resultat avant la manche suivante
const DELAI_CARTE     = 560;    // entre deux cartes distribuees
const DELAI_BANQUE    = 950;    // entre deux cartes de la banque
const DELAI_BOT       = 1300;   // temps de reflexion d\'un bot
const CHAT_MAX        = 60;     // messages de chat conserves par table
const ABSENCE_MAX     = 15000;  // sans nouvelles, un joueur perd sa place
const SOLDE_DEPART    = 22;

/* ---------- le penalty ----------
   L\'echelle des gains : un but = on monte d\'un cran.
   Le joueur peut encaisser quand il veut ; s\'il rate, il perd sa mise.
   Le tirage se fait ICI, sur le serveur : impossible de tricher
   en bidouillant la page.                                          */
const ECHELLE_PENALTY  = [2, 4, 8, 16, 32, 64, 100];
const CHANCE_BUT       = 4700;   // sur 10000, soit 47 % de buts (53 % d\'arrets)
const MISE_MINI_PENALTY = 0.10;
const ZONES_PENALTY    = 15;     // la cage est decoupee en 5 x 3
const DEFAITES_SECRET  = 2;      // apres deux echecs, la tete du gardien compte

/* ---------- le jeu du periph ----------
   Douze portes de la Porte Dauphine a Saint-Denis. A chaque porte
   franchie la somme monte ; au bout du parcours elle vaut cinquante
   fois la mise. Le joueur peut encaisser a chaque porte.
   La course se joue dans la page, mais l\'argent se compte ICI :
   la mise part au depart, le gain n\'est verse que par ce fichier, et
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
const MARGE_TEMPS      = 0.80;          // on tolere un peu de retard d\'horloge

/* la voiture de la boutique : plus rapide, avec des vrais freins */
const PRIX_VOITURE_PREMIUM     = 1200;
const VOITURE_PREMIUM_INDICE   = 4;
const VITESSE_MAX_PERIPH_PREMIUM = 300 / 3.6;   // metres par seconde

/* ---------- le periph en multijoueur ----------
   Une file d\'attente toute simple : des qu\'un deuxieme joueur reel la
   rejoint, un compte a rebours de dix secondes demarre pour tout le
   monde. S\'il redescend a moins de deux avant la fin, on annule, sans
   frais pour personne. Au top depart, chacun est debite et sa course
   demarre exactement comme en solo (meme fonction interne). Un petit
   groupe de course garde ensuite, pendant la course, la progression
   annoncee par chacun : ca ne sert qu\'a dessiner la voiture des autres
   joueurs, jamais a calculer un gain (ca, c\'est toujours les routes
   /api/periph-porte, /api/periph-encaisser, /api/periph-perdu, inchangees). */
const DUREE_ATTENTE_PERIPH_MULTI = 10000;
const EXPIRATION_COURSE_MULTI    = 5 * 60000;   // filet de securite

/* ---------- Tower Rush ----------
   Un etage se balance sous la grue ; le joueur appuie pour le lacher.
   Comme pour le periph, la balancoire s\'anime dans la page pour que ce
   soit fluide, mais le moment exact du lacher n\'est jamais cru sur
   parole : ce fichier garde l\'heure a laquelle CHAQUE balancement a
   commence (compte.tower.swingStart) et recalcule lui-meme, a la
   milliseconde pres, ou en etait le balancement quand la demande est
   arrivee. La precision, le multiplicateur et le risque d\'effondrement
   sont donc entierement decides ici, jamais par la page. */
const MISE_MINI_TOWER = 0.10;
const MISE_MAXI_TOWER = 500;

function towerAmpFor(n)    { return Math.max(15, 48 - n * 2.3); }
function towerPeriodFor(n) { return Math.max(0.55, 1.5 - n * 0.045); }
function towerRand(a, b) { return a + Math.random() * (b - a); }
function towerClamp(v, a, b) { return Math.max(a, Math.min(b, v)); }

/* ---------- Tower Rush : les cotes (refonte v2, casino beaucoup plus dur) ----------
   La seule facon de perdre la tour reste un lacher mal vise. Mais la cote
   tiree a chaque etage bien pose est maintenant tres majoritairement
   defavorable : bien plus souvent en dessous de x1 qu'au-dessus de x2/x3.
   Repartition (independante a chaque etage) :
     62 % : x0,25 a x0,95  (perte partielle, le cas de loin le plus frequent)
     25 % : x0,95 a x1,30  (quasi neutre)
     10 % : x1,30 a x2,00  (bon coup)
      3 % : x2,00 a x3,60  (gros coup, rare)
   Esperance ~0,90 par etage : monter beaucoup exige d'enchainer plusieurs
   bons coups d'affilee, ce qui devient vite tres improbable (simulation :
   multiplier une mise par plus de x32, comme un x0,10€->16 000 €, arrive
   environ 1 tour sur 4 000 a 5 000, quel que soit le niveau de jeu).
   Plus on monte, plus le balancement est rapide (towerPeriodFor) et
   l\'amplitude reduite (towerAmpFor) : viser juste devient plus dur en
   hauteur, ce qui ajoute un risque d\'echec qui grimpe avec l\'audace du
   joueur, en plus de l\'esperance deja negative du multiplicateur.
   Plafond de securite : niveau 30 ou x5000, encaisse d\'office (au-dela
   c\'est purement theorique - avec cette esperance, personne n\'en approche
   sans une serie de coups exceptionnelle).                              */
const TOWER_NIVEAUX  = 30;
const TOWER_MULT_MAX = 5000;

function towerRollFactor() {
  const r = Math.random();
  if (r < 0.62) return towerRand(0.25, 0.95);   // perte partielle : le cas le plus frequent
  if (r < 0.87) return towerRand(0.95, 1.30);   // quasi neutre
  if (r < 0.97) return towerRand(1.30, 2.00);   // bon coup
  return towerRand(2.00, 3.60);                  // gros coup, rare
}

/* Un lacher, calcule entierement ici. Modifie `tour` et renvoie l\'issue :
   'rate' (l\'etage part a cote, seulement si le lacher est mal vise) ou
   'pose'. Exporte en bas de fichier pour la simulation des cotes. */
function towerTirer(tour, angle) {
  const n = tour.floors.length;
  const niveau = tour.niveau | 0;
  const amp = towerAmpFor(n);
  const etaitGele = tour.frozenLeft > 0;
  if (etaitGele) angle *= 0.2;

  const errRatio = Math.abs(angle) / amp;
  /* zone de lacher sans risque : il faut vraiment mal viser (pres du
     bout du balancement) pour que l'etage parte a cote. En dessous de
     safeT, aucun risque, quel que soit le niveau deja atteint. */
  const safeT = 0.60, missT = Math.max(0.85, 1.08 - n * 0.012);
  const edgeT = towerClamp((errRatio - safeT) / Math.max(0.001, missT - safeT), 0, 1);
  const missChance = etaitGele ? 0 : edgeT * edgeT;
  if (Math.random() < missChance) return { issue: 'rate', angle: angle };

  const facteur = etaitGele ? towerRand(0.92, 1.06) : towerRollFactor();
  if (etaitGele) tour.frozenLeft--;
  else tour.niveau = niveau + 1;
  const parfait = !etaitGele && errRatio < 0.1 && facteur >= 1;

  // pas d\'arrondi ici : seul le gain final (mise x totalMult) est arrondi
  tour.totalMult = Math.min(TOWER_MULT_MAX, tour.totalMult * facteur);
  // les etages s'empilent bien droits : plus d'inclinaison qui s'accumule
  tour.leanSum = 0;
  tour.visOffset = 0;
  tour.floors.push({ mult: facteur, lean: 0 });

  // etage gele une fois toutes les ~14 etages en moyenne, pour souffler un peu
  if (!etaitGele && Math.random() < 0.07) tour.frozenLeft = 2 + (Math.random() < 0.5 ? 0 : 1);

  const sommet = tour.niveau >= TOWER_NIVEAUX || tour.totalMult >= TOWER_MULT_MAX;
  return { issue: 'pose', angle: angle, facteur: facteur, parfait: parfait, sommet: sommet };
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
   Les comptes sont ranges dans une base Upstash, jointe par simple
   requete web, pour qu\'ils survivent quand l\'hebergeur eteint et
   rallume le site. Aucune bibliotheque a installer.
   Si aucune base n\'est configuree, le site fonctionne quand meme :
   les comptes sont simplement gardes en memoire jusqu\'au prochain
   redemarrage. Le jeu n\'est jamais bloque par la base.
   =================================================================== */
const Carnet = {
  url: null,
  token: null,
  pret: false,
  memoire: new Map(),        // repli, et copie de travail
  indexMemoire: new Map(),   // repli pour l\'index de tous les joueurs

  async demarrer() {
    const url   = String(process.env.UPSTASH_REDIS_REST_URL   || '').replace(/\/+$/, '');
    const token = String(process.env.UPSTASH_REDIS_REST_TOKEN || '');

    if (!url || !token) {
      console.log('Carnet : aucune base configuree.');
      console.log('Le jeu tourne, mais les comptes seront perdus au redemarrage.');
      return;
    }
    this.url = url;
    this.token = token;
    try {
      const r = await this.commande(['PING']);
      if (r && r.result) {
        this.pret = true;
        console.log('Carnet : base connectee, les comptes sont conserves.');
      } else {
        console.log('Carnet : la base a repondu quelque chose d\'inattendu.');
      }
    } catch (e) {
      console.log('Carnet : connexion a la base impossible (' + e.message + ').');
      console.log('Le jeu tourne quand meme, mais les comptes ne seront pas conserves.');
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
      // SETNX n\'ecrit que si le pseudo est encore libre
      const r = await this.commande(['SETNX', 'joueur:' + fiche.pseudoBas, JSON.stringify(fiche)]);
      return !!(r && Number(r.result) === 1);
    } catch (e) {
      console.log('Carnet : creation impossible (' + e.message + ')');
      return true;                                // on laisse quand meme jouer
    }
  },

  // Enregistre l\'avancement. N\'interrompt jamais la partie : si la base
  // ne repond pas, on note l\'echec et le jeu continue.
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

  // Banni / debanni un compte par son pseudo (en minuscules). Utilise par
  // le code reserve au bannissement : ecrit directement dans la fiche
  // stockee, sans passer par enregistrer() qui a besoin d\'un compte en
  // ligne avec toutes ses stats.
  async definirBanni(pseudoBas, banni) {
    const ancienne = this.memoire.get(pseudoBas) || (await this.lire(pseudoBas)) || null;
    if (!ancienne) return false;
    const fiche = Object.assign({}, ancienne, { banni: !!banni });
    this.memoire.set(pseudoBas, fiche);
    if (!this.pret) return true;
    try {
      await this.commande(['SET', 'joueur:' + pseudoBas, JSON.stringify(fiche)]);
      return true;
    } catch (e) {
      console.log('Carnet : bannissement non enregistre (' + e.message + ')');
      return true;   // deja applique en memoire, effectif sur ce serveur
    }
  },

  // Change directement le solde d\'une fiche (utilise par le code admin pour
  // retirer l\'argent gagne en trichant, sans avoir a bannir le compte).
  async definirSolde(pseudoBas, solde) {
    const ancienne = this.memoire.get(pseudoBas) || (await this.lire(pseudoBas)) || null;
    if (!ancienne) return false;
    const fiche = Object.assign({}, ancienne, { solde: solde });
    this.memoire.set(pseudoBas, fiche);
    if (!this.pret) return true;
    try {
      await this.commande(['SET', 'joueur:' + pseudoBas, JSON.stringify(fiche)]);
      return true;
    } catch (e) {
      console.log('Carnet : modification du solde non enregistree (' + e.message + ')');
      return true;
    }
  },

  // Supprime completement un compte (fiche + entree d\'index). Utilise par
  // le code admin pour effacer les faux comptes crees par un bot.
  async supprimer(pseudoBas) {
    this.memoire.delete(pseudoBas);
    this.indexMemoire.delete(pseudoBas);
    if (!this.pret) return true;
    try {
      await this.commande(['DEL', 'joueur:' + pseudoBas]);
      const r = await this.commande(['GET', 'index:joueurs']);
      let index = {};
      if (r && r.result) { try { index = JSON.parse(r.result); } catch (e) { index = {}; } }
      delete index[pseudoBas];
      await this.commande(['SET', 'index:joueurs', JSON.stringify(index)]);
      return true;
    } catch (e) {
      console.log('Carnet : suppression non enregistree (' + e.message + ')');
      return true;
    }
  },

  // Tient un seul index { pseudoBas: {pseudo, creeLe, vuLe} } pour pouvoir
  // lister tous les joueurs deja crees (le code reserve au proprietaire
  // s\'en sert). On ne le touche qu\'a la creation du compte et a la
  // connexion, jamais a chaque appel : inutile de solliciter la base pour ca.
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
      console.log('Carnet : mise a jour de l\'index impossible (' + e.message + ')');
      const ancienne = this.indexMemoire.get(pseudoBas) || {};
      this.indexMemoire.set(pseudoBas, { pseudo, creeLe: ancienne.creeLe || maintenant, vuLe: maintenant });
    }
  },

  // Certains comptes ont ete crees avant que cet index existe (ou n\'ont
  // jamais reserve pour se reconnecter depuis) : on les retrouve tous en
  // listant les fiches "joueur:*" directement, et on reconstruit l\'index
  // en entier a partir d\'elles pour que la date "vu" reste juste (la
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
      console.log('Carnet : reconciliation de l\'index impossible (' + e.message + ')');
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
      console.log('Carnet : lecture de l\'index impossible (' + e.message + ')');
      return Array.from(this.indexMemoire.entries()).map(([pseudoBas, v]) => Object.assign({ pseudoBas }, v));
    }
  }
};

/* ---------- mots de passe : jamais stockes en clair ---------- */
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

/* ===================================================================
   POKER - Texas Hold\'em sans limite, uniquement entre vrais joueurs
   -------------------------------------------------------------------
   Meme principe que le blackjack : le serveur tient les cartes, les
   tours et le chronometre ; le battement fait avancer la donne.
   - Pas de bots, jamais. Moins de deux joueurs : la table attend.
   - Les jetons d\'un joueur, c\'est son vrai solde : chaque mise est
     debitee tout de suite, le pot est verse au(x) gagnant(s) a la fin.
   - Aucune commission (pas de rake) : tout le pot revient aux joueurs.
   - Les cartes privees d\'un joueur ne quittent JAMAIS le serveur vers
     un autre joueur, sauf a l\'abattage si ce joueur ne s\'est pas couche.
   Tous les montants de la donne sont comptes en CENTIMES (entiers)
   pour qu\'aucun centime ne se perde en route.
   =================================================================== */
const POKER_PLACES          = 6;
const POKER_PB_C            = 10;     // petite blinde : 0,10 EUR
const POKER_GB_C            = 20;     // grosse blinde : 0,20 EUR
const DUREE_DECOMPTE_POKER  = 10000;  // avant la premiere donne
const DUREE_PAROLE_POKER    = 20000;  // temps pour parler
const DUREE_RESULTAT_POKER  = 7000;   // pause entre deux donnes
const DELAI_CARTE_POKER     = 330;    // par carte distribuee
const PAUSE_RAMASSAGE_POKER = 900;    // les mises rejoignent le pot
const PAUSE_FLOP_POKER      = 1500;
const PAUSE_RUE_POKER       = 1100;   // turn / river
const PAUSE_TAPIS_POKER     = 2000;   // on deroule sans enchere (tapis)
const PAUSE_ABATTAGE_POKER  = 1800;

function neuveTablePoker(id, nom) {
  return {
    id, nom, jeu: 'poker', skin: 'or', mini: POKER_GB_C / 100,
    places: new Array(POKER_PLACES).fill(null),
    phase: 'attente', echeance: 0,
    bouton: -1, donne: 0, main: null, resultat: null,
    message: '', chat: [], chatId: 0, version: 1
  };
}

/* ---------- cartes : entier 0..51 ; rang = (c>>2)+2 ; couleur = c&3 ---------- */
const pkRang = c => (c >> 2) + 2, pkCouleur = c => c & 3;
function pkEval5(cs) {
  const r = [pkRang(cs[0]), pkRang(cs[1]), pkRang(cs[2]), pkRang(cs[3]), pkRang(cs[4])].sort((a, b) => b - a);
  const s0 = pkCouleur(cs[0]);
  const flush = pkCouleur(cs[1]) === s0 && pkCouleur(cs[2]) === s0 && pkCouleur(cs[3]) === s0 && pkCouleur(cs[4]) === s0;
  const cnt = {};
  for (const x of r) cnt[x] = (cnt[x] || 0) + 1;
  const g = Object.keys(cnt).map(Number).sort((a, b) => (cnt[b] - cnt[a]) || (b - a));
  let sh = 0;
  if (g.length === 5) {
    if (r[0] - r[4] === 4) sh = r[0];
    else if (r[0] === 14 && r[1] === 5 && r[4] === 2) sh = 5;   // roue A-2-3-4-5
  }
  let k;
  if (sh && flush) k = [8, sh];
  else if (cnt[g[0]] === 4) k = [7, g[0], g[1]];
  else if (cnt[g[0]] === 3 && cnt[g[1]] === 2) k = [6, g[0], g[1]];
  else if (flush) k = [5].concat(r);
  else if (sh) k = [4, sh];
  else if (cnt[g[0]] === 3) k = [3, g[0], g[1], g[2]];
  else if (cnt[g[0]] === 2 && cnt[g[1]] === 2) k = [2, g[0], g[1], g[2]];
  else if (cnt[g[0]] === 2) k = [1, g[0], g[1], g[2], g[3]];
  else k = [0].concat(r);
  let score = 0;
  for (let i = 0; i < 6; i++) score = score * 16 + (k[i] || 0);
  return { score, cat: k[0], k };
}
const PK_COMB = {};
function pkCombos(n) {
  if (PK_COMB[n]) return PK_COMB[n];
  const out = [];
  const rec = (start, acc) => {
    if (acc.length === 5) { out.push(acc.slice()); return; }
    for (let i = start; i < n; i++) { acc.push(i); rec(i + 1, acc); acc.pop(); }
  };
  rec(0, []);
  return PK_COMB[n] = out;
}
function pkMeilleure(cards) {
  let best = null;
  for (const idx of pkCombos(cards.length)) {
    const five = idx.map(i => cards[i]);
    const e = pkEval5(five);
    if (!best || e.score > best.score) { best = e; best.cards = five; }
  }
  return best;
}
const PK_NS = {2:'2',3:'3',4:'4',5:'5',6:'6',7:'7',8:'8',9:'9',10:'10',11:'Valet',12:'Dame',13:'Roi',14:'As'};
const PK_NP = {2:'2',3:'3',4:'4',5:'5',6:'6',7:'7',8:'8',9:'9',10:'10',11:'Valets',12:'Dames',13:'Rois',14:'As'};
const pkDe = r => r === 14 ? "d\'As" : 'de ' + PK_NP[r];
function pkNomMain(h) {
  const k = h.k;
  switch (h.cat) {
    case 8: return k[1] === 14 ? 'Quinte flush royale' : 'Quinte flush hauteur ' + PK_NS[k[1]];
    case 7: return 'Carre ' + pkDe(k[1]);
    case 6: return 'Full aux ' + PK_NP[k[1]] + ' par les ' + PK_NP[k[2]];
    case 5: return 'Couleur hauteur ' + PK_NS[k[1]];
    case 4: return 'Suite hauteur ' + PK_NS[k[1]];
    case 3: return 'Brelan ' + pkDe(k[1]);
    case 2: return 'Double paire, ' + PK_NP[k[1]] + ' et ' + PK_NP[k[2]];
    case 1: return 'Paire ' + pkDe(k[1]);
    default: return 'Hauteur ' + PK_NS[k[1]];
  }
}
function pkPaquet() {
  const d = [];
  for (let i = 0; i < 52; i++) d.push(i);
  for (let i = 51; i > 0; i--) { const j = crypto.randomInt(i + 1); const t = d[i]; d[i] = d[j]; d[j] = t; }
  return d;
}

/* ---------- petits outils ---------- */
const cts = e => Math.round(Number(e) * 100);          // euros -> centimes
const eurC = c => eur(c / 100);                          // centimes -> "1,20 EUR"
function pkStack(table, i) { const p = table.places[i]; return p ? cts(p.solde) : 0; }
function pkSuivant(from, pred) {
  for (let k = 1; k <= POKER_PLACES; k++) { const i = (from + k + POKER_PLACES) % POKER_PLACES; if (pred(i)) return i; }
  return -1;
}
function pkEnMain(table) {
  const m = table.main, out = [];
  if (!m) return out;
  m.joueurs.forEach((j, i) => { if (j && !j.couche) out.push(i); });
  return out;
}
function pkPeutParler(table) {
  const m = table.main, out = [];
  if (!m) return out;
  m.joueurs.forEach((j, i) => { if (j && !j.couche && !j.tapis) out.push(i); });
  return out;
}
function pkEligibles(table) {
  const out = [];
  table.places.forEach((p, i) => { if (p && p.type === 'humain' && cts(p.solde) >= 1) out.push(i); });
  return out;
}
function pkHumains(table) { return table.places.filter(p => p && p.type === 'humain').length; }
function pkLabel(j, txt, cls) { j.action = txt ? { txt, cls: cls || '' } : null; }

/* verse de l\'argent a un joueur de la donne, meme s\'il a quitte la table
   entre-temps (il ne perd jamais ce qui lui revient) */
function pkCrediter(table, i, c) {
  if (c <= 0) return;
  const j = table.main.joueurs[i];
  j.gain += c;
  const p = table.places[i];
  if (p && p.jeton === j.jeton) {
    p.solde = sous((cts(p.solde) + c) / 100);
    majSoldeCompte(p);
    return;
  }
  const compte = comptes.get(j.jeton) || [...comptes.values()].find(x => x.pseudo === j.nom);
  if (compte) {
    compte.solde = sous((cts(compte.solde) + c) / 100);
    const info = siegeDe(compte);
    if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
    Carnet.enregistrer(compte);
  }
}

/* pose un montant devant le joueur : il quitte VRAIMENT son solde */
function pkPoser(table, i, montantC) {
  const j = table.main.joueurs[i], p = table.places[i];
  if (!j || !p) return 0;
  const a = Math.max(0, Math.min(Math.round(montantC), cts(p.solde)));
  p.solde = sous((cts(p.solde) - a) / 100);
  majSoldeCompte(p);
  j.mise += a; j.total += a;
  if (cts(p.solde) === 0) j.tapis = true;
  return a;
}

/* ---------- une nouvelle donne ---------- */
function pkNouvelleDonne(table) {
  const elig = pkEligibles(table);
  if (elig.length < 2) {
    table.main = null; table.resultat = null;
    table.phase = 'attente';
    dire(table, 'En attente d\'un deuxieme joueur.');
    touche(table);
    return;
  }
  const joueurs = new Array(POKER_PLACES).fill(null);
  for (const i of elig) {
    const p = table.places[i];
    joueurs[i] = {
      jeton: p.jeton, nom: p.nom, cartes: [], mise: 0, total: 0,
      couche: false, tapis: false, aParle: false, bloque: false,
      montre: false, action: null, gain: 0, nomMain: '', depart: cts(p.solde)
    };
  }
  table.donne++;
  table.resultat = null;
  table.bouton = pkSuivant(table.bouton < 0 ? POKER_PLACES - 1 : table.bouton, i => !!joueurs[i]);
  const duo = elig.length === 2;
  const pb = duo ? table.bouton : pkSuivant(table.bouton, i => !!joueurs[i]);
  const gb = pkSuivant(pb, i => !!joueurs[i]);
  table.main = {
    joueurs, paquet: pkPaquet(), board: [], rue: 0,
    miseCourante: 0, relanceMin: POKER_GB_C, actif: -1, pb, gb
  };
  const m = table.main;
  pkPoser(table, pb, POKER_PB_C); pkLabel(joueurs[pb], 'P. blinde');
  pkPoser(table, gb, POKER_GB_C); pkLabel(joueurs[gb], 'G. blinde');
  m.miseCourante = POKER_GB_C;
  m.relanceMin = POKER_GB_C;

  // deux tours de distribution, en partant de la petite blinde
  let n = 0;
  for (let tour = 0; tour < 2; tour++) {
    let s = pb;
    for (let k = 0; k < elig.length; k++) {
      joueurs[s].cartes.push(m.paquet.pop()); n++;
      s = pkSuivant(s, i => !!joueurs[i]);
    }
  }
  table.phase = 'distribution';
  table.echeance = Date.now() + 700 + n * DELAI_CARTE_POKER;
  dire(table, 'Donne n°' + table.donne + ' : les cartes sont distribuees.');
  touche(table);
}

/* ---------- qui doit parler ? ---------- */
function pkOptions(table, i) {
  const m = table.main, j = m.joueurs[i];
  const stack = pkStack(table, i);
  const aSuivre = Math.max(0, m.miseCourante - j.mise);
  const maxTo = j.mise + stack;
  const autres = m.joueurs.some((o, k) => o && k !== i && !o.couche && !o.tapis);
  const minTo = m.miseCourante + m.relanceMin;
  const peutRelancer = !j.bloque && autres && maxTo > m.miseCourante;
  return {
    aSuivre, maxTo, minTo: Math.min(minTo, maxTo), peutRelancer,
    peutChecker: aSuivre === 0, montantSuivre: Math.min(aSuivre, stack)
  };
}

function pkProchain(table, depuis) {
  const m = table.main;
  if (pkEnMain(table).length <= 1) return pkFinTour(table);
  const ca = pkPeutParler(table);
  if (ca.length === 0) return pkFinTour(table);
  if (ca.every(i => m.joueurs[i].aParle && m.joueurs[i].mise === m.miseCourante)) return pkFinTour(table);
  if (ca.length === 1 && m.joueurs[ca[0]].mise >= m.miseCourante) return pkFinTour(table);
  for (let k = 0; k < POKER_PLACES; k++) {
    const i = (depuis + k) % POKER_PLACES, j = m.joueurs[i];
    if (j && !j.couche && !j.tapis && !(j.aParle && j.mise === m.miseCourante)) {
      m.actif = i;
      table.phase = 'parole';
      table.echeance = Date.now() + DUREE_PAROLE_POKER;
      dire(table, j.nom + ' a la parole.');
      touche(table);
      return;
    }
  }
  pkFinTour(table);
}

function pkDemarrerEncheres(table, depuis) {
  for (const j of table.main.joueurs) if (j) { j.aParle = false; j.bloque = false; }
  pkProchain(table, depuis);
}

function pkFinTour(table) {
  const m = table.main;
  m.actif = -1;
  const desMises = m.joueurs.some(j => j && j.mise > 0);
  table.phase = 'ramassage';
  table.echeance = Date.now() + (desMises ? PAUSE_RAMASSAGE_POKER : 350);
  touche(table);
}

/* ---------- une action d\'un joueur (ou du chronometre) ---------- */
function pkAgir(table, i, d) {
  const m = table.main, j = m.joueurs[i];
  const o = pkOptions(table, i);
  let type = d.type;
  if (type === 'tapis') {
    if (o.peutRelancer) { type = 'relancer'; d = { type, to: o.maxTo }; }
    else type = o.peutChecker ? 'checker' : 'suivre';
  }
  if (type === 'checker' && !o.peutChecker) type = 'suivre';
  if (type === 'relancer' && !o.peutRelancer) type = o.peutChecker ? 'checker' : 'suivre';

  if (type === 'coucher') {
    j.couche = true; pkLabel(j, 'Couche', 'fold');
  } else if (type === 'checker') {
    pkLabel(j, 'Check');
  } else if (type === 'suivre') {
    const a = pkPoser(table, i, o.aSuivre);
    pkLabel(j, j.tapis ? 'Tapis' : 'Suit ' + eurC(a), j.tapis ? 'allin' : '');
  } else if (type === 'relancer') {
    let to = Math.round(Number(d.to));
    if (!isFinite(to)) to = o.minTo;
    if (to >= o.maxTo) to = o.maxTo;
    else if (to < o.minTo) to = o.minTo;
    const avant = m.miseCourante;
    pkPoser(table, i, to - j.mise);
    const inc = to - avant;
    if (inc >= m.relanceMin) {
      m.relanceMin = inc;
      for (const q of m.joueurs) if (q && q !== j) { q.aParle = false; q.bloque = false; }
    } else if (inc > 0) {
      // relance incomplete (tapis court) : ne rouvre pas les relances
      for (const q of m.joueurs) if (q && q !== j) { if (q.aParle) q.bloque = true; q.aParle = false; }
    }
    if (to > m.miseCourante) m.miseCourante = to;
    pkLabel(j, j.tapis ? 'Tapis' : (avant === 0 ? 'Mise ' : 'Relance ') + eurC(to), j.tapis ? 'allin' : 'raise');
  }
  j.aParle = true;
  touche(table);
  pkProchain(table, (i + 1) % POKER_PLACES);
}

/* ---------- entre deux tours d\'encheres ---------- */
function pkApresRamassage(table) {
  const m = table.main;
  for (const j of m.joueurs) if (j) j.mise = 0;
  m.miseCourante = 0;
  m.relanceMin = POKER_GB_C;
  if (pkEnMain(table).length <= 1) return pkConclure(table);
  if (m.rue >= 3) {
    pkReveler(table);
    table.phase = 'abattage';
    table.echeance = Date.now() + PAUSE_ABATTAGE_POKER;
    dire(table, 'Abattage : les cartes sont retournees.');
    touche(table);
    return;
  }
  m.rue++;
  const n = m.rue === 1 ? 3 : 1;
  for (let k = 0; k < n; k++) m.board.push(m.paquet.pop());
  for (const j of m.joueurs) if (j && !j.couche) j.action = null;
  const encheres = pkPeutParler(table).length >= 2;
  if (!encheres) pkReveler(table);          // tout le monde est a tapis : on montre et on deroule
  table.phase = 'rue';
  table.echeance = Date.now() + (encheres ? (m.rue === 1 ? PAUSE_FLOP_POKER : PAUSE_RUE_POKER) : PAUSE_TAPIS_POKER);
  dire(table, ['', 'Le flop.', 'Le turn.', 'La river.'][m.rue]);
  touche(table);
}

function pkReveler(table) {
  for (const i of pkEnMain(table)) table.main.joueurs[i].montre = true;
}

/* ---------- les pots (principal + annexes), en centimes ---------- */
function pkPots(table) {
  const m = table.main;
  const tous = [];
  m.joueurs.forEach((j, i) => { if (j) tous.push(i); });
  const cont = pkEnMain(table);
  const levels = [...new Set(cont.map(i => m.joueurs[i].total))].sort((a, b) => a - b);
  const pots = []; let prev = 0;
  for (const L of levels) {
    let amt = 0;
    for (const i of tous) { const t = m.joueurs[i].total; amt += Math.min(t, L) - Math.min(t, prev); }
    const elig = cont.filter(i => m.joueurs[i].total >= L);
    if (amt > 0) pots.push({ amount: amt, elig });
    prev = L;
  }
  const totalPot = tous.reduce((a, i) => a + m.joueurs[i].total, 0);
  const reste = totalPot - pots.reduce((a, x) => a + x.amount, 0);
  if (reste > 0 && pots.length) pots[pots.length - 1].amount += reste;
  const fusion = [];
  for (const pt of pots) {
    const last = fusion[fusion.length - 1];
    if (last && last.elig.length === pt.elig.length && last.elig.every(i => pt.elig.includes(i))) last.amount += pt.amount;
    else fusion.push({ amount: pt.amount, elig: pt.elig.slice() });
  }
  return fusion;
}

/* ---------- fin de la donne : le pot va au(x) gagnant(s) ---------- */
function pkConclure(table) {
  const m = table.main;
  m.actif = -1;
  const J = m.joueurs;
  const cont = pkEnMain(table);
  const potTotal = J.reduce((a, j) => a + (j ? j.total : 0), 0);
  const res = { titre: '', sous: '', lignes: [], gagnants: [], cartesGagnantes: [] };
  const nomDe = i => J[i].nom;

  if (cont.length === 0) {
    // tout le monde est parti : chacun recupere ce qu\'il avait mis
    J.forEach((j, i) => { if (j) pkCrediter(table, i, j.total); });
    res.titre = 'Donne annulee';
    res.sous = 'Tout le monde a quitte la table : les mises sont rendues.';
  } else if (cont.length === 1) {
    const w = cont[0];
    pkCrediter(table, w, potTotal);
    res.gagnants = [w];
    res.titre = nomDe(w) + ' remporte ' + eurC(potTotal);
    res.sous = 'Tous les autres joueurs se sont couches.';
  } else {
    pkReveler(table);
    const ev = {};
    for (const i of cont) {
      ev[i] = pkMeilleure(J[i].cartes.concat(m.board));
      J[i].nomMain = pkNomMain(ev[i]);
      pkLabel(J[i], J[i].nomMain, 'hand');
    }
    const pots = pkPots(table);
    const principal = [];
    pots.forEach((pt, idx) => {
      if (pt.elig.length === 1) {
        const w = pt.elig[0];
        pkCrediter(table, w, pt.amount);
        res.lignes.push(['Mise non suivie rendue', nomDe(w) + ' · ' + eurC(pt.amount)]);
        return;
      }
      let best = -1;
      for (const i of pt.elig) best = Math.max(best, ev[i].score);
      const ws = pt.elig.filter(i => ev[i].score === best);
      ws.sort((a, b) => ((a - table.bouton + POKER_PLACES - 1) % POKER_PLACES) - ((b - table.bouton + POKER_PLACES - 1) % POKER_PLACES));
      const part = Math.floor(pt.amount / ws.length);
      let r = pt.amount - part * ws.length;
      for (const w of ws) { pkCrediter(table, w, part + (r > 0 ? 1 : 0)); if (r > 0) r--; }
      if (!principal.length) principal.push(...ws);
      const nomPot = idx === 0 ? 'Pot principal' : 'Pot annexe' + (pots.length > 2 ? ' ' + idx : '');
      res.lignes.push([nomPot + ' · ' + eurC(pt.amount), ws.map(nomDe).join(' & ') + (ws.length > 1 ? ' (partage)' : '')]);
    });
    const gagnantsPrincipal = principal.length ? principal : (pots[0] ? pots[0].elig : cont);
    res.gagnants = gagnantsPrincipal.slice();
    const wh = ev[gagnantsPrincipal[0]];
    res.cartesGagnantes = wh.cards.slice();
    res.titre = gagnantsPrincipal.length > 1 ? 'Pot partage' : nomDe(gagnantsPrincipal[0]) + ' gagne ' + eurC(J[gagnantsPrincipal[0]].gain);
    res.sous = pkNomMain(wh);
  }

  // controle : tout le pot a bien ete reverse, au centime pres
  const verse = J.reduce((a, j) => a + (j ? j.gain : 0), 0);
  if (verse !== potTotal) console.log('POKER : pot ' + potTotal + ' c, verse ' + verse + ' c (table ' + table.id + ')');

  // chaque participant : statistiques et sauvegarde
  J.forEach(j => {
    if (!j) return;
    j.mise = 0;
    const c = comptes.get(j.jeton);
    if (!c) return;
    c.mains++;
    const net = j.gain - j.total;
    if (net > 0) c.gagnees++; else if (net < 0) c.perdues++;
    Carnet.enregistrer(c);
  });

  table.resultat = res;
  table.phase = 'resultat';
  table.echeance = Date.now() + DUREE_RESULTAT_POKER;
  dire(table, res.titre);
  touche(table);
}

/* ---------- un joueur quitte la table (volontairement ou non) ---------- */
function pkQuitter(table, i) {
  const p = table.places[i];
  if (!p) return;
  table.places[i] = null;
  const c = comptes.get(p.jeton);
  if (c) { c.table = null; c.siege = -1; Carnet.enregistrer(c); }
  const m = table.main;
  const enCours = m && ['distribution', 'parole', 'ramassage', 'rue', 'abattage'].includes(table.phase);
  if (enCours && m.joueurs[i] && !m.joueurs[i].couche) {
    const j = m.joueurs[i];
    j.couche = true;                       // ses mises restent dans le pot
    pkLabel(j, 'Parti', 'fold');
    if (table.phase === 'parole') {
      if (m.actif === i) pkProchain(table, (i + 1) % POKER_PLACES);
      else if (pkEnMain(table).length <= 1) pkFinTour(table);
    }
  }
  if (pkHumains(table) === 0) {
    if (m && enCours) pkConclure(table);   // rend l\'argent qui serait encore au milieu
    table.main = null; table.resultat = null;
    table.phase = 'attente';
    table.message = '';
    table.chat = []; table.chatId = 0;
  }
  touche(table);
}

/* ---------- le battement du poker ---------- */
function battementPoker(table, now) {
  // les absents perdent leur place (et se couchent s\'ils etaient en jeu)
  table.places.forEach((p, i) => {
    if (!p) return;
    const c = comptes.get(p.jeton);
    if (!c || now - c.vu > ABSENCE_MAX) pkQuitter(table, i);
  });

  const m = table.main;
  switch (table.phase) {
    case 'attente':
      if (pkEligibles(table).length >= 2) {
        table.phase = 'decompte';
        table.echeance = now + DUREE_DECOMPTE_POKER;
        dire(table, 'La partie commence dans dix secondes.');
        touche(table);
      }
      break;
    case 'decompte':
      if (pkEligibles(table).length < 2) {
        table.phase = 'attente';
        dire(table, 'En attente d\'un deuxieme joueur.');
        touche(table);
      } else if (now >= table.echeance) pkNouvelleDonne(table);
      break;
    case 'distribution':
      if (now >= table.echeance) {
        for (const j of m.joueurs) if (j && !j.couche && !/blinde/.test(j.action ? j.action.txt : '')) j.action = null;
        pkDemarrerEncheres(table, (m.gb + 1) % POKER_PLACES);
      }
      break;
    case 'parole':
      if (now >= table.echeance && m.actif >= 0) {
        const o = pkOptions(table, m.actif);
        pkAgir(table, m.actif, { type: o.peutChecker ? 'checker' : 'coucher' });
      }
      break;
    case 'ramassage':
      if (now >= table.echeance) pkApresRamassage(table);
      break;
    case 'rue':
      if (now >= table.echeance) {
        if (pkPeutParler(table).length >= 2 && pkEnMain(table).length >= 2) {
          pkDemarrerEncheres(table, (table.bouton + 1) % POKER_PLACES);
        } else pkApresRamassage(table);
      }
      break;
    case 'abattage':
      if (now >= table.echeance) pkConclure(table);
      break;
    case 'resultat':
      if (now >= table.echeance) pkNouvelleDonne(table);
      break;
  }
}

/* ---------- ce que voit UN joueur : jamais les cartes cachees des autres ---------- */
function etatPoker(table, jeton) {
  const now = Date.now();
  const compte = comptes.get(jeton);
  const moiIndex = table.places.findIndex(p => p && p.jeton === jeton);
  const moi = moiIndex >= 0 ? table.places[moiIndex] : null;
  const m = table.main;
  const enJeu = m && table.phase !== 'attente' && table.phase !== 'decompte';

  const places = table.places.map((p, i) => {
    const j0 = enJeu ? m.joueurs[i] : null;
    // la donne en cours ne concerne cette place que si c\'est bien le meme joueur
    const j = j0 && (!p || p.jeton === j0.jeton) ? j0 : null;
    // un joueur parti en pleine donne : sa place reste "fantome" jusqu\'a la fin
    if (!p && !(j && j.jeton)) return null;
    const estMoi = i === moiIndex;
    let cartes = [];
    if (j) {
      if (estMoi || j.montre) cartes = j.cartes.slice();        // les miennes, ou abattage
      else if (!j.couche) cartes = j.cartes.map(() => null);   // dos de cartes, rien d\'autre
    }
    return {
      nom: p ? p.nom : j.nom,
      moi: estMoi,
      humain: true,
      parti: !p,
      solde: p && (estMoi || p.soldeVisible) ? p.solde : null,
      soldeVisible: !!(p && p.soldeVisible),
      enMain: !!j,
      cartes,
      montre: !!(j && j.montre),
      mise: j ? j.mise / 100 : 0,
      total: j ? j.total / 100 : 0,
      couche: !!(j && j.couche),
      tapis: !!(j && j.tapis),
      action: j ? j.action : null,
      nomMain: j && j.montre ? j.nomMain : '',
      gain: j && table.phase === 'resultat' ? j.gain / 100 : 0
    };
  });

  let secondes = 0;
  if (['decompte', 'parole', 'resultat'].includes(table.phase)) {
    secondes = Math.max(0, Math.ceil((table.echeance - now) / 1000));
  }
  const monTour = !!(enJeu && table.phase === 'parole' && m.actif === moiIndex && moiIndex >= 0);
  let options = null;
  if (monTour) {
    const o = pkOptions(table, moiIndex);
    options = {
      aSuivre: o.aSuivre / 100, montantSuivre: o.montantSuivre / 100,
      minTo: o.minTo / 100, maxTo: o.maxTo / 100,
      peutRelancer: o.peutRelancer, peutChecker: o.peutChecker,
      maMise: m.joueurs[moiIndex].mise / 100
    };
  }
  // une fois la donne conclue, le pot a ete verse : il n\'y a plus rien au milieu
  const potTotal = enJeu && table.phase !== 'resultat' ? m.joueurs.reduce((a, j) => a + (j ? j.total : 0), 0) : 0;
  const misesDevant = enJeu ? m.joueurs.reduce((a, j) => a + (j ? j.mise : 0), 0) : 0;

  return {
    jeu: 'poker',
    version: table.version,
    table: table.id,
    nom: table.nom,
    skin: table.skin,
    phase: table.phase,
    secondes,
    dureeParole: DUREE_PAROLE_POKER / 1000,
    pb: POKER_PB_C / 100, gb: POKER_GB_C / 100,
    donne: table.donne,
    bouton: enJeu ? table.bouton : -1,
    actif: enJeu ? m.actif : -1,
    rue: enJeu ? m.rue : 0,
    board: enJeu ? m.board.slice() : [],
    miseCourante: enJeu ? m.miseCourante / 100 : 0,
    pot: (potTotal - misesDevant) / 100,
    potTotal: potTotal / 100,
    places,
    monIndex: moiIndex,
    monTour,
    options,
    monSolde: moi ? moi.solde : (compte ? compte.solde : 0),
    monSoldeVisible: !!(moi && moi.soldeVisible),
    resultat: table.phase === 'resultat' ? table.resultat : null,
    message: table.message,
    assis: moiIndex >= 0,
    chat: chatPour(table, jeton)
  };
}

const tables = [
  neuveTable('majorelle', 'Jardin Majorelle', 0.01, 'vert'),
  neuveTable('palmeraie', 'Palmeraie Royale', 0.01, 'or'),
  neuveTablePoker('poker', 'Martin\'s Poker')
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
   DEROULEMENT D\'UNE MANCHE
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
  // mise automatique pour les humains qui n\'ont rien pose
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

  if (actifs.length === 0) {                 // personne n\'a mise : on relance
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
    dire(table, p.nom + ' reflechit...');
  } else {
    table.phase = 'joueur';
    table.echeance = Date.now() + DUREE_TOUR;
    dire(table, p.mains.length > 1
      ? 'A vous de decider (main ' + (table.mainActive + 1) + ').'
      : 'A vous de decider.');
  }
  touche(table);
}

/* ---------- avance au prochain joueur/main a jouer. Gere le fait
   qu\'une place partagee (split) a deux mains a jouer l\'une apres
   l\'autre avant de passer a la place suivante. ---------- */
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
        texte = 'depasse 21, la banque encaisse ' + eur(m.mise);
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
        texte = 'egalite a ' + tm + ', mise rendue';
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
   LE BATTEMENT DE CŒUR - c\'est lui qui empeche tout blocage
   =================================================================== */
function battement() {
  const now = Date.now();

  for (const table of tables) {
    if (table.jeu === 'poker') { battementPoker(table, now); continue; }
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
        if (now >= table.echeance) {                // le joueur n\'a pas repondu : il reste
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
function chatPour(table, jeton) {
  return table.chat.map(m => ({
    id: m.id, nom: m.nom, texte: m.texte, systeme: !!m.systeme, t: m.t || 0,
    moi: !!(m.jeton && m.jeton === jeton),
    cadeau: m.cadeau ? {
      de: m.cadeau.de, a: m.cadeau.a, montant: m.cadeau.montant,
      pourMoi: m.cadeau.aJeton === jeton,     // c\'est moi qui recois
      deMoi:   m.cadeau.deJeton === jeton     // c\'est moi qui offre
    } : null
  }));
}

function etatPour(table, jeton) {
  if (table.jeu === 'poker') return etatPoker(table, jeton);
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
      // le solde des autres n\'est envoye que s\'ils ont choisi de l\'afficher
      solde: (estMoi || p.soldeVisible) ? p.solde : null,
      soldeVisible: !!p.soldeVisible
    };
  });

  const banque = table.banque.map((c, i) =>
    (i === 1 && !table.cacheeRevelee) ? null : c            // la carte cachee n\'est pas envoyee
  );

  let secondes = 0;
  if (table.phase === 'mise' || table.phase === 'joueur') {
    secondes = Math.max(0, Math.ceil((table.echeance - now) / 1000));
  }

  const provocation = !!(moi && moi.provocation);
  if (moi && moi.provocation) moi.provocation = false;       // on ne la montre qu\'une fois

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
    chat: chatPour(table, jeton)
  };
}

function resumeSalon() {
  return tables.map(t => ({
    id: t.id,
    nom: t.nom,
    jeu: t.jeu || 'blackjack',
    mini: t.mini,
    skin: t.skin,
    pb: t.jeu === 'poker' ? POKER_PB_C / 100 : undefined,
    gb: t.jeu === 'poker' ? POKER_GB_C / 100 : undefined,
    phase: t.phase,
    places: t.places.map(p => p ? { nom: p.nom, bot: p.type === 'bot' } : null),
    joueurs: t.places.filter(p => p && p.type === 'humain').length
  }));
}

/* ===================================================================
   ROULETTE - une seule table partagee, le serveur tient l\'economie
   -------------------------------------------------------------------
   Ajout autonome : aucune fonction du blackjack ci-dessus n\'est
   modifiee. La table de roulette vit dans son propre objet, avec son
   propre battement (setInterval separe) et ses propres routes
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
   LE PERIPH - depart d\'une course, en solo comme en multijoueur
   -------------------------------------------------------------------
   Factorise pour que la route /api/periph-demarrer (solo, inchangee)
   et le demarrage d\'un groupe multijoueur debitent la mise et ouvrent
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
   LE PERIPH EN MULTIJOUEUR - file d\'attente et groupes de course
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

/* ce que la page d\'un joueur voit des AUTRES joueurs reels de sa course.
   "age" = depuis combien de millisecondes la position annoncee a ete
   mesuree sur la page de ce joueur (trajet aller compris). */
function autresMembresPeriph(compte) {
  if (!compte.periphMulti) return [];
  const g = groupesCoursePeriph.get(compte.periphMulti.groupeId);
  if (!g) return [];
  const maintenant = Date.now();
  return Object.keys(g.membres)
    .filter(j => j !== compte.jetonRef)
    .map(j => {
      const m = g.membres[j];
      const d = typeof m.d === 'number' ? Math.max(m.d, distancePeriph(m.palier)) : distancePeriph(m.palier);
      const mesure = m.mesure || m.maj || maintenant;
      return { pseudo: m.pseudo, couleur: m.couleur, voiture: m.voiture, palier: m.palier, fraction: m.fraction,
               d: d, v: m.statut === 'course' ? (m.v || 0) : 0, age: Math.max(0, maintenant - mesure),
               x: m.x || 0, maj: m.maj || 0, statut: m.statut };
    });
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
      compte.periphMultiErreur = 'Solde insuffisant : la course a demarre sans vous.';
      return;
    }
    const voiture = demarrerCourseInterne(compte, entree.mise, entree.voiture);
    compte.periphMulti = { groupeId: id, couleur: entree.couleurAffectee };
    membres[j] = {
      pseudo: compte.pseudo, couleur: entree.couleurAffectee,
      palier: 0, fraction: 0, d: 0, v: 0, statut: 'course', maj: Date.now(),
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
      groupeEnFormationPeriph = null;                 // annule : personne n\'est debite
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
   LE BOIS DE BOULOGNE - la sortie a droite de la Porte Dauphine
   -------------------------------------------------------------------
   Pendant le periph, avant la Porte Maillot, on peut tourner a droite.
   La mise du periph passe alors dans la poursuite de Toledo (ni gagnee,
   ni perdue a ce moment-la). Seuls de vrais joueurs y vont : jusqu'a 4,
   reunis pendant un decompte de 15 s. Toledo part au bout du decompte,
   les policiers 3 s apres lui.
   Le trajet de Toledo est tire ici avec une graine (planToledo) et
   recalcule a l'identique par chaque page : il est au meme endroit sur
   tous les ecrans. Ses points de vie, eux, ne sont comptes qu'ici :
   chaque coup annonce par une page est verifie contre ce trajet.
   S'il tombe avant la sortie du bois : cent fois la mise pour chaque
   policier encore en course. Sinon, la mise est perdue.
   =================================================================== */
const BOIS_VIE           = 600;       // seul ; +300 par joueur en plus
const BOIS_MULT          = 100;
const BOIS_ATTENTE       = 15000;
const BOIS_MAX           = 4;
const BOIS_DEPART_POLICE = 3000;      // les policiers partent 3 s apres Toledo
const BOIS_SORTIE_MIN    = 460;       // metres depuis la Porte Dauphine
const BOIS_DEGAT_CHOC    = 25;
const BOIS_DEGAT_BALLE   = 40;
const BOIS_BALLES        = 5;
const BOIS_VITESSE_MAX   = 330 / 3.6; // metres par seconde, turbo compris (marge au-dessus des 300 km/h de la voiture premium)

function planToledo(graine){
  let s=graine>>>0;
  const r=()=>{ s=(s+0x6D2B79F5)|0; let t=Math.imul(s^(s>>>15),1|s);
    t=(t+Math.imul(t^(t>>>7),61|t))^t; return ((t^(t>>>14))>>>0)/4294967296; };
  const PAS=50, VOIE=3.5, DIST=3500;
  const voieX=k=>(k-1.5)*VOIE;
  const objets=[], bananes=[];
  for(let d=260; d<DIST-160; d+=380+r()*140)
    objets.push({d:d, x:voieX(Math.floor(r()*4)), genre:r()<0.5?'pistolet':'turbo'});
  for(let d=320; d<DIST-80; d+=230+r()*100){
    const x=voieX(Math.floor(r()*4))+(r()-0.5)*0.8;
    if(!objets.some(o=>o.d-d<20&&d-o.d<20)) bananes.push({d:d, x:x});
  }
  const D=[], X=[], V=[], bombes=[];
  let voie=Math.floor(r()*4), d=25, v=0, x=voieX(voie);
  let tEv=0, vCible=0, tVoie=2500, tBombe=12000+r()*3000, freinage=false;
  let k=0, tFin=0;
  while(k<12000){
    const t=k*PAS;
    if(t<9000){ vCible=t/9000*175; freinage=false; }
    else if(t>=tEv){
      const a=r(), base=196+20*Math.min(1,(t-9000)/25000);
      freinage=false;
      if(a<0.18){ vCible=base+40+r()*10; tEv=t+1000+r()*600; }                  // il accélère d'un coup
      else if(a<0.30){ vCible=base-40+r()*10; tEv=t+800+r()*500; freinage=true; } // il ralentit
      else { vCible=base-8+r()*16; tEv=t+1500+r()*1500; }                        // croisière
    }
    if(t>=tVoie){
      let n=Math.floor(r()*3); if(n>=voie) n++;
      voie=n; tVoie=t+(freinage?700:1200)+r()*(freinage?500:1800);
    }
    const dv=vCible-v, pasV=(dv>0?45:80)*PAS/1000;
    v=dv>0?Math.min(vCible,v+pasV):Math.max(vCible,v-pasV);
    const xc=voieX(voie), dx=xc-x, pasX=6*PAS/1000;
    x=dx>0?Math.min(xc,x+pasX):Math.max(xc,x-pasX);
    D.push(d); X.push(x); V.push(v);
    if(t>=tBombe){ bombes.push({t:t, d:d-0.6, x:x}); tBombe=t+4500+r()*3000; }
    if(d>=DIST){ tFin=t; break; }
    d+=v/3.6*PAS/1000;
    k++;
  }
  if(!tFin) tFin=k*PAS;
  return {PAS, D, X, V, bombes, objets, bananes, tFin, DIST};
}
/* position de Toledo à l'instant t, avec ses grosses accélérations (quand on
   l'abîme trop) : chacune le fait avancer plus vite pendant quelques secondes */
function etatToledo(p,t,boosts){
  let e;
  if(t<=0) e={d:p.D[0], x:p.X[0], v:0};
  else {
    const f=t/p.PAS, i=Math.floor(f);
    if(i>=p.D.length-1){ const n=p.D.length-1; e={d:p.D[n]+(t-n*p.PAS)*p.V[n]/3600, x:p.X[n], v:p.V[n]}; }
    else { const a=f-i; e={d:p.D[i]+(p.D[i+1]-p.D[i])*a, x:p.X[i]+(p.X[i+1]-p.X[i])*a, v:p.V[i]+(p.V[i+1]-p.V[i])*a}; }
  }
  if(boosts) for(const b of boosts){
    const dt=Math.max(0,Math.min(b.dur,t-b.t));
    if(dt>0){ e.d+=b.dv/3.6*dt/1000; if(t-b.t<b.dur) e.v+=b.dv; }
  }
  return e;
}

const fileBois = [];                    // jetons en attente, dans l'ordre d'arrivee
const formationsBois = [];              // {echeance, jetons:[...]}
const groupesBois = new Map();          // id -> {graine, plan, depart, vie, statut, pris, membres}
let   compteurGroupeBois = 1;

function groupeBoisDe(compte) {
  return compte.bois && compte.bois.groupeId ? groupesBois.get(compte.bois.groupeId) || null : null;
}
function formationBoisDe(jeton) {
  return formationsBois.find(f => f.jetons.indexOf(jeton) >= 0) || null;
}
/* un joueur quitte le bois en route (autre jeu, page fermee) : sa mise est perdue */
function abandonnerBois(compte) {
  if (!compte.bois) return;
  const g = groupeBoisDe(compte);
  if (g && !compte.bois.fini && g.membres[compte.jetonRef]) g.membres[compte.jetonRef].statut = 'crash';
  formationsBois.forEach(f => { const i = f.jetons.indexOf(compte.jetonRef); if (i >= 0) f.jetons.splice(i, 1); });
  compte.bois = null;
  Carnet.enregistrer(compte);
}

function demarrerGroupeBois(jetons) {
  const id = 'b' + (compteurGroupeBois++);
  const graine = crypto.randomInt(1, 2147483647);
  const membres = {};
  let slot = 0;
  jetons.forEach(j => {
    const c = comptes.get(j);
    if (!c || !c.bois || c.bois.groupeId) return;
    c.bois.groupeId = id;
    c.bois.slot = slot;
    c.bois.balles = 0;
    membres[j] = { pseudo: c.pseudo, slot: slot, voiture: c.bois.voiture, d: 0, x: (slot - 1.5) * 3.5, v: 0,
                   mesure: Date.now(), maj: Date.now(), statut: 'course', dernierChoc: 0, dernierTir: 0, gain: 0 };
    slot++;
  });
  if (!slot) return;
  /* plus il y a de policiers, plus Toledo est solide */
  const vieMax = BOIS_VIE + 300 * (slot - 1);
  groupesBois.set(id, { graine, plan: planToledo(graine), depart: Date.now(), vie: vieMax, vieMax,
                        seuil: vieMax * 0.75, boosts: [], statut: 'course', pris: [], membres });
}

/* Toledo est tombe : cent fois la mise pour chaque policier encore en course */
function gagnerBois(g) {
  if (g.statut !== 'course') return;
  g.statut = 'gagne';
  Object.keys(g.membres).forEach(j => {
    const m = g.membres[j];
    if (m.statut !== 'course') return;
    const c = comptes.get(j);
    if (!c || !c.bois) return;
    const gain = sous(c.bois.mise * BOIS_MULT);
    c.solde = sous(c.solde + gain);
    m.gain = gain;
    m.statut = 'gagne';
    c.bois.fini = true;
    const info = siegeDe(c);
    if (info && info.p) { info.p.solde = c.solde; touche(info.table); }
    Carnet.enregistrer(c);
  });
}
/* Toledo est sorti du bois : la mise des policiers restants est perdue */
function perdreBois(g) {
  if (g.statut !== 'course') return;
  g.statut = 'perdu';
  Object.keys(g.membres).forEach(j => {
    const m = g.membres[j];
    if (m.statut === 'course') m.statut = 'perdu';
    const c = comptes.get(j);
    if (c && c.bois && c.bois.groupeId) { c.bois.fini = true; Carnet.enregistrer(c); }
  });
}

function battementBois() {
  const now = Date.now();
  // les joueurs de la file qui ne donnent plus de nouvelles perdent leur place (et leur mise)
  for (let i = fileBois.length - 1; i >= 0; i--) {
    const c = comptes.get(fileBois[i]);
    if (!c || !c.bois || now - c.vu > ABSENCE_MAX) {
      if (c) abandonnerBois(c);
      fileBois.splice(i, 1);
    }
  }
  for (let i = formationsBois.length - 1; i >= 0; i--) {
    const f = formationsBois[i];
    f.jetons = f.jetons.filter(j => fileBois.indexOf(j) >= 0);
    if (!f.jetons.length) { formationsBois.splice(i, 1); continue; }
    if (now >= f.echeance) {
      f.jetons.forEach(j => { const k = fileBois.indexOf(j); if (k >= 0) fileBois.splice(k, 1); });
      demarrerGroupeBois(f.jetons);
      formationsBois.splice(i, 1);
    }
  }
  groupesBois.forEach((g, id) => {
    if (g.statut === 'course' && etatToledo(g.plan, now - g.depart - 400, g.boosts).d >= g.plan.DIST) perdreBois(g);
    /* Toledo ne se laisse pas doubler : si un policier passe devant lui de plus
       de quelques metres, il remet un coup d'accelerateur pour repasser devant (annonce a
       toutes les pages 0,7 s a l'avance, pour que tout le monde le voie pareil) */
    if (g.statut === 'course') {
      const ecoule = now - g.depart;
      const enCourse = Object.values(g.membres).filter(m => m.statut === 'course');
      if (enCourse.length && ecoule > BOIS_DEPART_POLICE + 4000) {
        const enTete = Math.max(...enCourse.map(m => dBoisEstimee(m, now)));
        const T = etatToledo(g.plan, ecoule, g.boosts);
        const ecart = enTete - (T.d + 2.3);
        const dejaEnBoost = g.boosts.some(b => ecoule < b.t + b.dur);
        if (ecart > 3 && !dejaEnBoost && now - (g.derniereFuite || 0) > 2500 && T.d < g.plan.DIST - 150) {
          g.boosts.push({ t: ecoule + 600, dur: 2600, dv: Math.min(100, 55 + ecart * 1.6) });
          g.derniereFuite = now;
        }
      }
    }
    // un policier qui ne donne plus signe de vie pendant la course est hors course
    Object.keys(g.membres).forEach(j => {
      const m = g.membres[j];
      if (m.statut === 'course' && now - m.maj > ABSENCE_MAX) {
        m.statut = 'crash';
        const c = comptes.get(j);
        if (c && c.bois) { c.bois = null; Carnet.enregistrer(c); }
      }
    });
    if (g.statut === 'course' && !Object.values(g.membres).some(m => m.statut === 'course')) g.statut = 'perdu';
    if (g.statut !== 'course' && now - g.depart > g.plan.tFin + 60000) groupesBois.delete(id);
  });
}
setInterval(battementBois, 200);

/* la position d'un policier, prolongee jusqu'a maintenant avec sa vitesse */
function dBoisEstimee(m, now) {
  return m.d + (m.v || 0) / 3.6 * Math.max(0, Math.min(2000, now - (m.mesure || now))) / 1000;
}
function autresMembresBois(compte, g) {
  const now = Date.now();
  return Object.keys(g.membres).filter(j => j !== compte.jetonRef).map(j => {
    const m = g.membres[j];
    return { slot: m.slot, pseudo: m.pseudo, voiture: m.voiture, d: m.d, x: m.x,
             v: m.statut === 'course' ? m.v : 0, age: Math.max(0, now - (m.mesure || now)), statut: m.statut };
  });
}
function etatBoisPour(compte, g) {
  const m = g.membres[compte.jetonRef];
  return { membres: autresMembresBois(compte, g), vie: g.vie, vieMax: g.vieMax, boosts: g.boosts, statut: g.statut,
           moi: m ? m.statut : 'crash', gain: m ? m.gain : 0, pris: g.pris,
           balles: compte.bois ? compte.bois.balles : 0, ecoule: Date.now() - g.depart, solde: compte.solde };
}

/* ===================================================================
   LE PONT DE CRISTAL - solo et multijoueur
   -------------------------------------------------------------------
   Le serveur tire seul, au depart, quelle(s) vitre(s) tient/tiennent
   a chaque rangee. La page ne fait que choisir une vitre et animer la
   reponse. Les cotes (tables solo et duo) sont celles du prototype
   valide : retour moyen toujours sous 1 euro par euro mise.
   =================================================================== */
const MODES_PONT = {
  prudent:   { largeur: 3, solides: 2, rangees: 9,
               solo: [1.44, 2.12, 3.08, 4.40, 6.30, 8.90, 12.60, 17.80, 25.00],
               duo:  [1.20, 1.44, 1.72, 2.05, 2.45, 2.90, 3.45, 4.10, 4.90] },
  classique: { largeur: 2, solides: 1, rangees: 7,
               solo: [1.92, 3.72, 7.10, 13.40, 24.80, 45.00, 80.00],
               duo:  [1.38, 1.90, 2.60, 3.60, 4.90, 6.60, 9.00] },
  audacieux: { largeur: 3, solides: 1, rangees: 5,
               solo: [2.85, 8.20, 22.50, 55.00, 100.00],
               duo:  [1.70, 2.85, 4.80, 8.00, 13.50] }
};
const MISE_MINI_PONT = 0.10, MISE_MAXI_PONT = 200;
const DUREE_ATTENTE_PONT_MULTI = 10000;
const PONT_MULTI_MAX = 3;
const EXPIRATION_PONT_MULTI = 10 * 60000;   // filet de securite

/* un pont : pour chaque rangee, un tableau de booleens (vitre solide ?) */
function tirerPont(m) {
  const rangs = [];
  for (let k = 0; k < m.rangees; k++) {
    const ordre = [...Array(m.largeur).keys()];
    for (let i = ordre.length - 1; i > 0; i--) { const j = crypto.randomInt(i + 1); const t = ordre[i]; ordre[i] = ordre[j]; ordre[j] = t; }
    const solide = new Array(m.largeur).fill(false);
    ordre.slice(0, m.solides).forEach(j => { solide[j] = true; });
    rangs.push(solide);
  }
  return rangs;
}

function soldeAuSiege(compte) {
  const info = siegeDe(compte);
  if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
}

/* ---------- multijoueur : file d\'attente, puis salons ---------- */
const filePontMulti = [];              // {jeton, pseudo, mise, rejointLe}
let   groupeEnFormationPont = null;    // {echeance, jetons:[...]}
const salonsPont = new Map();          // id -> {creeLe, finiLe, rangs, revele, casses, membres:{jeton:{...}}}
let   compteurSalonPont = 1;

function retirerDeLaFilePont(jeton) {
  const i = filePontMulti.findIndex(e => e.jeton === jeton);
  if (i >= 0) filePontMulti.splice(i, 1);
}

function salonPontDe(compte) {
  if (!compte.pontMulti) return null;
  return salonsPont.get(compte.pontMulti.salonId) || null;
}

/* ce que chaque membre voit du salon : le pont connu de tous, et ou en est chacun */
function vuePontMulti(compte, g) {
  const m = MODES_PONT.classique;
  return {
    statut: 'parti', salonId: compte.pontMulti.salonId, ecoule: Date.now() - g.creeLe,
    rangees: m.rangees, largeur: m.largeur, cotes: m.duo,
    revele: g.revele, casses: g.casses,
    membres: Object.keys(g.membres).map(j => {
      const x = g.membres[j];
      return { pseudo: x.pseudo, couleur: x.couleur, pos: x.pos, vitre: x.vitre, statut: x.statut,
               gain: x.gain, moi: j === compte.jetonRef };
    }),
    solde: compte.solde
  };
}

/* un joueur quitte un salon en pleine traversee : sa mise reste perdue */
function abandonnerPontMulti(compte) {
  const g = salonPontDe(compte);
  if (g && g.membres[compte.jetonRef] && g.membres[compte.jetonRef].statut === 'jeu') {
    g.membres[compte.jetonRef].statut = 'abandon';
  }
  compte.pontMulti = null;
}

function demarrerSalonPont(jetons) {
  const id = 'p' + (compteurSalonPont++);
  const m = MODES_PONT.classique;
  const rangs = tirerPont(m);
  const membres = {};
  let couleur = 0;
  jetons.forEach(j => {
    const entree = filePontMulti.find(e => e.jeton === j);
    const compte = comptes.get(j);
    retirerDeLaFilePont(j);
    if (!entree || !compte) return;
    if (entree.mise > compte.solde + 1e-9) {
      compte.pontMultiErreur = 'Solde insuffisant : la traversee a demarre sans vous.';
      return;
    }
    // la mise est prise au depart, comme au periph multijoueur
    compte.solde = sous(compte.solde - entree.mise);
    compte.pont = null;
    soldeAuSiege(compte);
    Carnet.enregistrer(compte);
    compte.pontMulti = { salonId: id };
    membres[j] = { pseudo: compte.pseudo, couleur: couleur++, mise: entree.mise,
                   pos: 0, vitre: -1, statut: 'jeu', gain: 0, maj: Date.now() };
  });
  if (Object.keys(membres).length) {
    salonsPont.set(id, {
      creeLe: Date.now(), finiLe: 0, rangs: rangs,
      revele: new Array(m.rangees).fill(null),          // vitre solide, une fois la rangee foulee par quelqu\'un
      casses: Array.from({ length: m.rangees }, () => []), // vitres brisees sous quelqu\'un
      membres: membres
    });
  }
}

function battementPontMulti() {
  const now = Date.now();
  for (let i = filePontMulti.length - 1; i >= 0; i--) {
    const c = comptes.get(filePontMulti[i].jeton);
    if (!c || now - c.vu > ABSENCE_MAX) filePontMulti.splice(i, 1);
  }

  if (groupeEnFormationPont) {
    const g = groupeEnFormationPont;
    g.jetons = g.jetons.filter(j => filePontMulti.some(e => e.jeton === j));
    // un troisieme joueur peut encore monter pendant le compte a rebours
    for (const e of filePontMulti) {
      if (g.jetons.length >= PONT_MULTI_MAX) break;
      if (g.jetons.indexOf(e.jeton) < 0) g.jetons.push(e.jeton);
    }
    if (g.jetons.length < 2) {
      groupeEnFormationPont = null;                  // annule : personne n\'est debite
    } else if (now >= g.echeance) {
      demarrerSalonPont(g.jetons);
      groupeEnFormationPont = null;
    }
  } else if (filePontMulti.length >= 2) {
    groupeEnFormationPont = {
      echeance: now + DUREE_ATTENTE_PONT_MULTI,
      jetons: filePontMulti.slice(0, PONT_MULTI_MAX).map(e => e.jeton)
    };
  }

  salonsPont.forEach((g, id) => {
    Object.keys(g.membres).forEach(j => {
      const x = g.membres[j], c = comptes.get(j);
      if (x.statut === 'jeu' && (!c || now - c.vu > ABSENCE_MAX)) x.statut = 'abandon';
    });
    const actif = Object.values(g.membres).some(x => x.statut === 'jeu');
    if (!actif && !g.finiLe) g.finiLe = now;
    if ((!actif && now - g.finiLe > 15000) || now - g.creeLe > EXPIRATION_PONT_MULTI) salonsPont.delete(id);
  });
}
setInterval(battementPontMulti, 200);

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
// vue selon l\'index (voir Carnet.indexerJoueur). Les plus recemment vus
// d\'abord.
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
    return { pseudo: j.pseudo, pseudoBas: j.pseudoBas, creeLe: j.creeLe || null, vuLe: vuLe, enLigne: enLigne };
  });
  joueurs.sort((a, b) => new Date(b.vuLe || 0) - new Date(a.vuLe || 0));
  return joueurs;
}

/* Codes de verification email - stockes en memoire avec expiration.
   (une seule liste pour tout le serveur, et un seul nettoyage par minute) */
const codesVerification = new Map();  // pseudo -> { code, email, expire }

async function envoyerEmailVerification(email, pseudo, code) {
  console.log('[EMAIL] DEBUT - email:', email, 'pseudo:', pseudo);

  const gmailUser = process.env.GMAIL_USER;
  const gmailPassword = process.env.GMAIL_PASSWORD;

  console.log('[EMAIL] GMAIL_USER existe:', !!gmailUser, 'valeur:', gmailUser);
  console.log('[EMAIL] GMAIL_PASSWORD existe:', !!gmailPassword);

  if (!gmailUser || !gmailPassword) {
    console.log('[EMAIL] Variables GMAIL manquantes : pas d\'email envoye');
    return false;
  }

  try {
    console.log('[EMAIL] Creation transporter...');
    const transporter = nodemailer.createTransport({
      service: 'gmail',
      /* sur l'hebergement gratuit, la connexion est bloquee : on n'attend pas des minutes */
      connectionTimeout: 7000, greetingTimeout: 7000, socketTimeout: 9000,
      auth: {
        user: gmailUser,
        pass: gmailPassword
      }
    });
    console.log('[EMAIL] Transporter cree OK');

    const mailOptions = {
      from: gmailUser,
      to: email,
      subject: 'Verifiez votre compte Casino Messina',
      html: `
        <h2>Bienvenue sur Casino Messina !</h2>
        <p>Votre code de verification est : <strong style="font-size: 24px; color: #d4af37;">${code}</strong></p>
        <p>Veuillez entrer ce code pour activer votre compte.</p>
        <p>Ce code expire dans 10 minutes.</p>
      `
    };

    console.log('[EMAIL] Appel transporter.sendMail...');
    const result = await transporter.sendMail(mailOptions);
    console.log('[EMAIL] SUCCESS! messageId:', result.messageId);
    return true;
  } catch (e) {
    console.log('[EMAIL] CATCH EXCEPTION:', e.message);
    console.log('[EMAIL] Stack trace:', e.stack);
    return false;
  }
}

/* Nettoyage periodique des codes expires */
setInterval(() => {
  const now = Date.now();
  for (const [pseudo, data] of codesVerification.entries()) {
    if (data.expire < now) codesVerification.delete(pseudo);
  }
}, 60000);  // toutes les minutes



/* ===================================================================
   RAZZIA - le jeu de conquete sur la vraie carte de Paris
   -------------------------------------------------------------------
   Chaque joueur pose sa base sur un vrai batiment du secteur ouest
   (16e, Trocadero, Bois de Boulogne, Boulogne-Billancourt, bord du 15e).
   Il achete des koalas (100 EUR), des pistolets (un pistolet = un koala arme),
   les repartit sur les 4 cotes de sa base et envoie jusqu'a 4 groupes
   dans les vraies rues, a pied ou par le metro.
   Une base pillee perd 25 % du vrai solde du casino (partage entre
   les allies qui attaquent ensemble) et brule 30 minutes.
   Tout le monde est ici, dans un seul "monde" garde dans la base Upstash.
   =================================================================== */
/* nu = koala sans arme ; pistolet = pistolet noir ; diamant = pistolet noir diamant rouge (le mieux) */
const RZ_TYPES = ['nu', 'pistolet', 'diamant'];
const RZ_FORCE = { nu: 1, pistolet: 4, diamant: 10 };
const RZ_PRIX  = { koala: 100, pistolet: 600, diamant: 2500 };
const RZ_NIV_ARME = { pistolet: 1, diamant: 2 };                            // niveau d'armurerie requis
const RZ_PRIX_ARMURERIE = [2000, 12000];                                    // pour passer au niveau 1, puis 2
const RZ_ARMURERIE_MAX  = RZ_PRIX_ARMURERIE.length;
const RZ_PRIX_DEFENSE   = [0, 2000, 6000, 15000, 40000];                   // index = niveau actuel (1 a 4)
const RZ_MAX_GROUPES = 10;
const RZ_PILLAGE     = 0.25;
const RZ_FEU         = 30 * 60 * 1000;
const RZ_REPARATION  = 5000;
const RZ_BOUCLIER_ATTENTE = 12 * 3600 * 1000;   // 12 h avant de pouvoir remettre le bouclier
const RZ_V_PIED      = 14;      // metres par seconde (le temps du jeu est accelere)
const RZ_V_METRO     = 60;      // deux fois plus rapide qu'avant
const RZ_V_LIMOUSINE = RZ_V_METRO * 2;   // la limousine va deux fois plus vite que le metro
const RZ_PRIX_LIMOUSINE = 45000;         // EUR, achat unique et definitif
const RZ_DUREE_MAX   = 540;     // 9 minutes au plus, d'un bout a l'autre de la carte
const RZ_REVENU      = 0.01;    // EUR par koala et par minute a un poste tenu (100 koalas = 1 EUR/min)
/* plus un joueur tient de postes differents en meme temps, plus chacun rapporte : */
const RZ_CONTROLE_MULT = [1, 1, 2, 4, 7, 12, 18, 26, 36, 48];   // index = nb de postes distincts tenus (0 a 9)
function rzMultControle(nb) { return RZ_CONTROLE_MULT[Math.max(0, Math.min(nb, RZ_CONTROLE_MULT.length - 1))]; }
/* les postes a tenir pour gagner de l'argent, eparpilles dans toute la zone :
   meme mecanique partout, seul l'emplacement change. */
const RZ_POSTES = [
  { id: 'batb',  nom: 'Bat B',        lon: 2.27890, lat: 48.85270 },   // Maison de la Radio, au milieu du secteur
  { id: 'nord',  nom: 'Poste Nord',   lon: 2.25980, lat: 48.88460 },   // vers le Pont de Neuilly
  { id: 'est',   nom: 'Poste Est',    lon: 2.29820, lat: 48.87810 },   // vers les Ternes
  { id: 'sud',   nom: 'Poste Sud',    lon: 2.27850, lat: 48.83650 },   // vers Auteuil
  { id: 'ouest', nom: 'Poste Ouest',  lon: 2.23800, lat: 48.83210 },   // vers Boulogne-Billancourt
  { id: 'nordest', nom: 'Poste Nord-Est', lon: 2.28900, lat: 48.88900 },  // vers Porte Maillot
  { id: 'sudest',  nom: 'Poste Sud-Est',  lon: 2.28500, lat: 48.82300 },  // vers Auteuil-sud
  { id: 'sudouest',nom: 'Poste Sud-Ouest',lon: 2.23500, lat: 48.81900 },  // vers Boulogne-sud
  { id: 'centre',  nom: 'Poste Centre',   lon: 2.23000, lat: 48.86200 },  // dans le bois, cote Boulogne-Billancourt
];
function rzPoste(id) { return RZ_POSTES.find(p => p.id === id) || RZ_POSTES[0]; }

/* ---- les bandits (façon "barbares" de RoK) : des camps fixes, éparpillés
   dans toute la zone, à attaquer pour de l'argent. Niveau 1 à 5 : plus le
   niveau est haut, plus ils se défendent, plus le butin est gros. Battus,
   ils reviennent (niveau retiré au hasard) après RZ_BANDIT_RESPAWN. */
const RZ_BANDIT_FORCE   = [8, 20, 40, 65, 100];                                   // defense par niveau (1 a 5)
const RZ_BANDIT_GAIN    = [[900, 1000], [2300, 2500], [4600, 5000], [7500, 8200], [11500, 12500]];
const RZ_BANDIT_RESPAWN = 10 * 60 * 1000;                                         // 10 minutes avant de reformer un camp vaincu
const RZ_BANDIT_POS = [
  [2.2743,48.8472], [2.2962,48.8656], [2.2372,48.8537], [2.2458,48.8619], [2.2973,48.8492],
  [2.2869,48.8355], [2.2817,48.8607], [2.2452,48.8151], [2.2644,48.8771], [2.2498,48.8473],
  [2.2704,48.8595], [2.2402,48.8352], [2.2863,48.8813], [2.2662,48.8269], [2.2467,48.8343],
  [2.2812,48.8675], [2.2534,48.8500], [2.2752,48.8847], [2.2835,48.8249], [2.2598,48.8580],
];
const RZ_BANDIT_NIVEAUX_INIT = [1,1,1,1,1,1,1, 2,2,2,2,2,2, 3,3,3,3, 4,4, 5];      // repartition de depart
const RZ_BANDITS = RZ_BANDIT_POS.map((p, i) => ({
  id: 'b' + i, lon: p[0], lat: p[1], niveau: RZ_BANDIT_NIVEAUX_INIT[i], mortJusqua: 0,
}));
function rzBanditNiveauAleatoire() {
  const r = Math.random();
  if (r < 0.35) return 1;
  if (r < 0.63) return 2;
  if (r < 0.83) return 3;
  if (r < 0.95) return 4;
  return 5;
}
function rzBanditVivant(b, now) { return !b.mortJusqua || b.mortJusqua <= now; }
/* revient tout seul, avec un niveau retire au hasard, une fois le delai passe */
function rzBanditRafraichir(b, now) {
  if (b.mortJusqua && b.mortJusqua <= now) { b.mortJusqua = 0; b.niveau = rzBanditNiveauAleatoire(); }
  return b;
}
const RZ_COTES       = ['devant', 'derriere', 'gauche', 'droite'];
const RZ_ZONE = [
  [2.2330,48.8680],[2.2500,48.8830],[2.2740,48.8900],[2.2960,48.8925],[2.3060,48.8790],
  [2.3085,48.8695],[2.3060,48.8580],[2.2970,48.8475],[2.2880,48.8320],[2.2840,48.8195],
  [2.2600,48.8105],[2.2400,48.8160],[2.2230,48.8260],[2.2220,48.8420],[2.2250,48.8560]
];
/* les stations de metro du secteur (le trace des lignes n'est jamais montre) */
const RZ_STATIONS = [
  ['Charles de Gaulle–Étoile',2.2950,48.8738],['Argentine',2.2894,48.8756],['Porte Maillot',2.2826,48.8781],
  ['Les Sablons',2.2718,48.8812],['Pont de Neuilly',2.2598,48.8846],['Victor Hugo',2.2858,48.8698],
  ['Porte Dauphine',2.2764,48.8716],['Ternes',2.2982,48.8781],['Kléber',2.2934,48.8715],
  ['Boissière',2.2900,48.8668],['Trocadéro',2.2871,48.8634],['Passy',2.2858,48.8575],
  ['Bir-Hakeim',2.2892,48.8539],['Dupleix',2.2935,48.8504],['La Motte-Picquet–Grenelle',2.2985,48.8496],
  ['Iéna',2.2939,48.8646],['Alma–Marceau',2.3010,48.8647],['Rue de la Pompe',2.2779,48.8641],
  ['La Muette',2.2740,48.8581],['Ranelagh',2.2700,48.8554],['Jasmin',2.2680,48.8524],
  ['Michel-Ange–Auteuil',2.2644,48.8479],['Michel-Ange–Molitor',2.2615,48.8449],['Exelmans',2.2598,48.8425],
  ['Porte de Saint-Cloud',2.2567,48.8378],['Marcel Sembat',2.2432,48.8338],['Billancourt',2.2380,48.8321],
  ['Pont de Sèvres',2.2303,48.8297],['Boulogne–Pont de Saint-Cloud',2.2285,48.8408],
  ['Boulogne–Jean Jaurès',2.2388,48.8421],['Porte d\'Auteuil',2.2582,48.8479],['Église d\'Auteuil',2.2690,48.8471],
  ['Chardon-Lagache',2.2670,48.8452],['Mirabeau',2.2730,48.8471],['Javel–André Citroën',2.2780,48.8462],
  ['Charles Michels',2.2858,48.8466],['Avenue Émile Zola',2.2950,48.8470],['Balard',2.2785,48.8365],
  ['Lourmel',2.2822,48.8388],['Boucicaut',2.2878,48.8410],['Félix Faure',2.2918,48.8427],['Commerce',2.2940,48.8447]
];

const RZJ = {};                 // pseudoBas -> joueur du jeu
const RZG = {};                 // id -> groupe de koalas hors de la base
let   rzCompteur = 1;
let   rzCharge   = false;

function rzVide() { return { nu: 0, pistolet: 0, diamant: 0 }; }
function rzPropre(u) { const r = rzVide(); RZ_TYPES.forEach(t => { r[t] = Math.max(0, Math.floor(Number(u && u[t]) || 0)); }); return r; }
function rzTotal(u) { return RZ_TYPES.reduce((s, t) => s + (u[t] | 0), 0); }
function rzPuissance(u) { return RZ_TYPES.reduce((s, t) => s + (u[t] | 0) * RZ_FORCE[t], 0); }
/* les plus faibles tombent en premier */
function rzPertes(u, aPerdre) {
  const r = Object.assign(rzVide(), u);
  for (const t of RZ_TYPES) while (aPerdre > 1e-9 && r[t] > 0) { r[t]--; aPerdre -= RZ_FORCE[t]; }
  return r;
}
/* purement mathematique : 101 contre 100, le premier gagne et garde 1 koala */
function rzCombat(A, multA, B, multB) {
  const pa = rzPuissance(A) * multA, pb = rzPuissance(B) * multB;
  if (pa > pb) return { gagnant: 'A', A: rzPertes(A, pb / multA), B: rzVide() };
  if (pb > pa) return { gagnant: 'B', A: rzVide(), B: rzPertes(B, pa / multB) };
  return { gagnant: 'nul', A: rzVide(), B: rzVide() };
}
/* un groupe qui perd une attaque ne se fait jamais rayer d'un coup : il perd
   au plus 30 % de sa force envoyee (les plus faibles d'abord) et le reste
   rentre tout seul a la base. */
const RZ_PERTE_MAX_DEFAITE = 0.30;
function rzApresDefaite(u) { return rzPertes(u, rzPuissance(u) * RZ_PERTE_MAX_DEFAITE); }
function rzMultDefense(j) { return 1 + 0.25 * ((j.defense || 1) - 1); }

/* ---- murailles : petits tronçons de mur qu'on chaine autour de sa base ----
   chaque tronçon coute cher, a la taille d'un batiment ou deux, et bloque le
   passage de tout groupe ennemi tant qu'il tient : pour traverser, il faut
   d'abord l'attaquer et le detruire. Plus on y stationne de koalas (renfort,
   definitif), plus il resiste. */
const RZ_MURS = {};                 // id -> { id, proprio, a:[lon,lat], b:[lon,lat], garnison }
let   rzMurCompteur = 1;
const RZ_MUR_COUT        = 500;     // EUR le tronçon
const RZ_MUR_REMBOURS    = 350;     // EUR rendus quand on demolit sa propre muraille
const RZ_MUR_LONGUEUR_MIN = 66;     // m (x1,7 de plus)
const RZ_MUR_LONGUEUR_MAX = 471;    // m (x1,7 de plus)
const RZ_MUR_CHAINE_MAX  = 510;     // m : doit se relier a la base ou a un mur deja pose
const RZ_MUR_VIE_BASE    = 30;      // force de base, meme sans renfort
const RZ_PORTAIL_COUT    = 1500;    // EUR : un tronçon qu'on peut ouvrir/fermer
const RZ_PORTAIL_VIE_BASE = 60;     // le portail encaisse plus qu'une simple muraille
function rzMurForce(m) { return (m.portail ? RZ_PORTAIL_VIE_BASE : RZ_MUR_VIE_BASE) + rzPuissance(m.garnison); }
/* intersection de segments (formule standard, orientation des triplets) */
function rzOrientation(a, b, c) { return (c[0] - a[0]) * (b[1] - a[1]) - (c[1] - a[1]) * (b[0] - a[0]); }
function rzSegCroise(p1, p2, p3, p4) {
  const d1 = rzOrientation(p3, p4, p1), d2 = rzOrientation(p3, p4, p2);
  const d3 = rzOrientation(p1, p2, p3), d4 = rzOrientation(p1, p2, p4);
  return ((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) && ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0));
}
/* le premier mur ennemi (intact, pas alliee) que ce chemin traverse, ou null.
   ignoreId : on ignore la muraille qu'on est justement en train d'attaquer. */
function rzMurSurChemin(proprio, coords, ignoreId) {
  for (const m of Object.values(RZ_MURS)) {
    if (m.id === ignoreId || m.proprio === proprio || rzAllies(proprio, m.proprio)) continue;
    if (m.portail && m.ouvert) continue;   // un portail ouvert laisse passer tout le monde
    for (let i = 1; i < coords.length; i++) if (rzSegCroise(coords[i - 1], coords[i], m.a, m.b)) return m;
  }
  return null;
}
/* repartit les koalas de la base sur les 4 cotes, selon les pourcentages choisis */
function rzRepartir(stock, rep) {
  const res = {}; RZ_COTES.forEach(c => { res[c] = rzVide(); });
  RZ_TYPES.forEach(t => {
    const n = stock[t] | 0; let cumulPct = 0, donne = 0;
    RZ_COTES.forEach(c => {
      cumulPct += (rep[c] || 0);
      const jusque = Math.round(n * cumulPct / 100);
      res[c][t] = Math.max(0, jusque - donne); donne = jusque;
    });
  });
  return res;
}

function rzDist(a, b) {           // a, b = [lon, lat], en metres
  const R = 6371000, r = Math.PI / 180;
  const dLat = (b[1] - a[1]) * r, dLon = (b[0] - a[0]) * r;
  const x = Math.sin(dLat / 2) ** 2 + Math.cos(a[1] * r) * Math.cos(b[1] * r) * Math.sin(dLon / 2) ** 2;
  return 2 * R * Math.asin(Math.sqrt(x));
}
function rzLongueur(coords) { let s = 0; for (let i = 1; i < coords.length; i++) s += rzDist(coords[i - 1], coords[i]); return s; }
/* la position actuelle d'un groupe, meme en route (interpole le long de ses
   etapes) : sert a intercepter des koalas qui se baladent, pas seulement
   ceux qui sont postes quelque part. Miroir exact de la fonction du meme
   nom cote client (position()), pour que le point d'attaque envoye colle
   a ce que le joueur voit sur sa carte. */
function rzPositionActuelle(g, now) {
  if (g.etat !== 'route' || !g.etapes || !g.etapes.length) return g.pos || null;
  const es = g.etapes;
  for (let i = 0; i < es.length; i++) {
    const e = es[i];
    if (now < e.t0) return e.type === 'pied' ? e.coords[0] : e.depuis;
    if (now <= e.t1) {
      const f = (now - e.t0) / Math.max(1, e.t1 - e.t0);
      if (e.type === 'metro') return [e.depuis[0] + (e.vers[0] - e.depuis[0]) * f, e.depuis[1] + (e.vers[1] - e.depuis[1]) * f];
      const L = rzLongueur(e.coords), vise = f * L; let fait = 0;
      for (let j = 1; j < e.coords.length; j++) {
        const d = rzDist(e.coords[j - 1], e.coords[j]);
        if (fait + d >= vise) {
          const h = d ? (vise - fait) / d : 0, a = e.coords[j - 1], b = e.coords[j];
          return [a[0] + (b[0] - a[0]) * h, a[1] + (b[1] - a[1]) * h];
        }
        fait += d;
      }
      return e.coords[e.coords.length - 1];
    }
  }
  const der = es[es.length - 1];
  return der.type === 'pied' ? der.coords[der.coords.length - 1] : der.vers;
}
function rzDansZone(p) {
  let dedans = false;
  for (let i = 0, j = RZ_ZONE.length - 1; i < RZ_ZONE.length; j = i++) {
    const xi = RZ_ZONE[i][0], yi = RZ_ZONE[i][1], xj = RZ_ZONE[j][0], yj = RZ_ZONE[j][1];
    if (((yi > p[1]) !== (yj > p[1])) && (p[0] < (xj - xi) * (p[1] - yi) / (yj - yi) + xi)) dedans = !dedans;
  }
  return dedans;
}
function rzPoint(p) {
  if (!Array.isArray(p) || p.length < 2) return null;
  const lon = Number(p[0]), lat = Number(p[1]);
  if (!isFinite(lon) || !isFinite(lat) || Math.abs(lon - 2.26) > 0.2 || Math.abs(lat - 48.85) > 0.2) return null;
  return [Math.round(lon * 1e6) / 1e6, Math.round(lat * 1e6) / 1e6];
}

function rzNouveauJoueur(compte) {
  return { pseudo: compte.pseudo, base: null, bouclier: true, bouclierRetireLe: 0, feuJusqua: 0,
           defense: 1, armurerie: 0, stock: rzVide(), limousine: false,
           repartition: { devant: 25, derriere: 25, gauche: 25, droite: 25 },
           allies: [], demandes: [], evenements: [] };
}
function rzJoueur(compte) {
  let j = RZJ[compte.pseudoBas];
  if (!j) { j = rzNouveauJoueur(compte); RZJ[compte.pseudoBas] = j; }
  j.pseudo = compte.pseudo;
  return j;
}
function rzEvenement(pb, texte, genre) {
  const j = RZJ[pb]; if (!j) return;
  j.evenements.push({ t: Date.now(), texte, genre: genre || 'info' });
  if (j.evenements.length > 25) j.evenements.splice(0, j.evenements.length - 25);
}
function rzAllies(a, b) { const j = RZJ[a]; return !!(j && j.allies.indexOf(b) >= 0); }
function rzEnFeu(j) { return (j.feuJusqua || 0) > Date.now(); }
function rzGroupesDe(pb) { return Object.values(RZG).filter(g => g.proprio === pb); }

/* ---- l'argent : le vrai solde du casino, que le joueur soit la ou non ---- */
function rzCompteEnLigne(pb) { for (const c of comptes.values()) if (c.pseudoBas === pb) return c; return null; }
async function rzSolde(pb) {
  const c = rzCompteEnLigne(pb); if (c) return c.solde;
  const f = await Carnet.lire(pb); return f ? (Number(f.solde) || 0) : 0;
}
async function rzAjouter(pb, delta) {
  const c = rzCompteEnLigne(pb);
  if (c) {
    c.solde = sous(Math.max(0, c.solde + delta));
    const info = siegeDe(c);
    if (info && info.p) { info.p.solde = c.solde; touche(info.table); }
    Carnet.enregistrer(c);
    return c.solde;
  }
  const f = await Carnet.lire(pb); if (!f) return null;
  f.solde = sous(Math.max(0, (Number(f.solde) || 0) + delta));
  Carnet.memoire.set(pb, f);
  if (Carnet.pret) Carnet.commande(['SET', 'joueur:' + pb, JSON.stringify(f)]).catch(() => {});
  return f.solde;
}

/* ---- sauvegarde du monde ----
   Deux soucis corriges ici :
   1) un echec reseau vers la base (Upstash) etait ignore sans nouvel essai ;
   2) pendant une mise en ligne (ou un redemarrage), Render fait tourner
      DEUX serveurs en meme temps, chacun avec sa copie du monde en memoire.
      L'admin supprimait la base sur l'un, le joueur tombait sur l'autre...
      et l'ancienne base revenait, impossible a deplacer.
   Maintenant chaque sauvegarde porte un numero de version, et un serveur
   qui voit dans la base une version plus recente que la sienne recharge
   le monde avant de repondre (toujours avant de poser ou supprimer une base). */
let rzSauvePrevue = null;
let rzADIRTY = false;      // il y a des changements pas encore confirmes sauvegardes
let rzEnCours = false;     // une tentative de sauvegarde est en cours
let rzVersion = 0;         // version du monde qu'on a en memoire
let rzDerniereSync = 0;
async function rzSauverMaintenant(sansVerif) {
  if (!Carnet.pret) { rzADIRTY = false; return true; }   // pas de base configuree : tout reste en memoire
  if (rzEnCours) { await new Promise(r => setTimeout(r, 300)); if (rzEnCours) return false; }
  rzEnCours = true;
  try {
    /* un autre serveur a ecrit plus recent que ce qu'on a vu : notre copie est
       perimee, on ne l'ecrase pas par-dessus, on recharge la sienne */
    if (!sansVerif) {
      const rv = await Carnet.commande(['GET', 'razzia:version']);
      if ((Number(rv && rv.result) || 0) > rzVersion) {
        const r = await Carnet.commande(['GET', 'razzia:monde']);
        if (r && r.result) { rzAppliquerMonde(JSON.parse(r.result)); rzADIRTY = false;
          console.log('Razzia : copie perimee abandonnee, monde recharge.'); return true; }
      }
    }
    const v = Math.max(Date.now(), rzVersion + 1);
    const bandits = RZ_BANDITS.map(b => ({ id: b.id, niveau: b.niveau, mortJusqua: b.mortJusqua }));
    await Carnet.commande(['MSET', 'razzia:monde', JSON.stringify({ joueurs: RZJ, groupes: RZG, n: rzCompteur, v, bandits, murs: RZ_MURS, mc: rzMurCompteur }), 'razzia:version', String(v)]);
    rzVersion = v;
    rzADIRTY = false;
    return true;
  } catch (e) {
    console.log('Razzia : sauvegarde impossible, nouvel essai bientot (' + e.message + ')');
    return false;
  } finally {
    rzEnCours = false;
  }
}
function rzSauver() {
  rzADIRTY = true;
  if (!rzCharge || rzSauvePrevue) return;
  rzSauvePrevue = setTimeout(async () => {
    rzSauvePrevue = null;
    await rzSauverMaintenant();
  }, 1500);
}
// filet de securite : une sauvegarde ratee est retentee toute seule
setInterval(() => { if (rzADIRTY && rzCharge) rzSauverMaintenant(); }, 20000);

function rzAppliquerMonde(d) {
  Object.keys(RZJ).forEach(k => delete RZJ[k]);
  Object.keys(RZG).forEach(k => delete RZG[k]);
  Object.assign(RZJ, d.joueurs || {}); Object.assign(RZG, d.groupes || {});
  // anciennes armes -> nouvelles (couteau = sans arme, grosses armes = diamant)
  const conv = u => { if (!u) return rzVide(); const r = rzVide();
    r.nu = (u.nu | 0) + (u.couteau | 0); r.pistolet = u.pistolet | 0; r.diamant = (u.diamant | 0) + (u.kalach | 0) + (u.roquette | 0); return r; };
  Object.values(RZJ).forEach(j => { j.stock = conv(j.stock); j.armurerie = Math.min(RZ_ARMURERIE_MAX, j.armurerie | 0); });
  Object.values(RZG).forEach(g => {
    g.unites = conv(g.unites);
    // ancien Bat B unique -> nouveau systeme de postes (celui-ci garde l'id 'batb')
    if (g.cible && g.cible.type === 'batb') g.cible = { type: 'poste', id: 'batb' };
  });
  rzCompteur = Math.max(rzCompteur, d.n || 1);
  rzVersion = Number(d.v) || 0;
  // les bandits : positions et niveaux de depart restent fixes dans le code,
  // seuls l'etat vaincu/niveau actuel sont restaures (par id)
  (d.bandits || []).forEach(sb => {
    const b = RZ_BANDITS.find(x => x.id === sb.id);
    if (b) { b.niveau = sb.niveau || b.niveau; b.mortJusqua = sb.mortJusqua || 0; }
  });
  Object.keys(RZ_MURS).forEach(k => delete RZ_MURS[k]);
  Object.assign(RZ_MURS, d.murs || {});
  rzMurCompteur = Math.max(rzMurCompteur, d.mc || 1);
}
/* se remettre a jour si un autre serveur a sauvegarde plus recent que nous.
   force = on va poser/supprimer une base : on verifie a coup sur. Sinon, au
   plus une verification toutes les 4 s (pour ne pas epuiser le quota Upstash). */
async function rzSynchroniser(force) {
  if (!Carnet.pret || !rzCharge) return;
  const now = Date.now();
  if (!force && now - rzDerniereSync < 4000) return;
  rzDerniereSync = now;
  try {
    const rv = await Carnet.commande(['GET', 'razzia:version']);
    const distante = Number(rv && rv.result) || 0;
    if (distante <= rzVersion) { if (rzADIRTY) await rzSauverMaintenant(true); return; }
    const r = await Carnet.commande(['GET', 'razzia:monde']);
    if (r && r.result) {
      rzAppliquerMonde(JSON.parse(r.result)); rzADIRTY = false;
      console.log('Razzia : monde recharge (version plus recente trouvee dans la base).');
    }
  } catch (e) { console.log('Razzia : synchronisation impossible (' + e.message + ')'); }
}
(async function rzCharger() {
  for (let i = 0; i < 30 && !Carnet.pret; i++) await new Promise(r => setTimeout(r, 1000));
  if (Carnet.pret) {
    try {
      const r = await Carnet.commande(['GET', 'razzia:monde']);
      if (r && r.result) rzAppliquerMonde(JSON.parse(r.result));
    } catch (e) { console.log('Razzia : lecture du monde impossible (' + e.message + ')'); }
  }
  rzCharge = true;
  rzDerniereSync = Date.now();
  console.log('Razzia : monde pret (' + Object.keys(RZJ).length + ' joueurs).');
})();

/* ---- les trajets ----
   Les etapes a pied suivent les vraies rues (calculees par la page).
   Le serveur recalcule lui-meme toutes les durees. */
function rzStation(nom) { return RZ_STATIONS.find(s => s[0] === nom) || null; }
function rzPlanifier(depart, arrivee, etapesBrutes, t0) {
  if (!Array.isArray(etapesBrutes) || !etapesBrutes.length || etapesBrutes.length > 5) return null;
  const etapes = [];
  for (const e of etapesBrutes) {
    if (e && e.type === 'pied') {
      const c = (Array.isArray(e.coords) ? e.coords : []).slice(0, 600).map(rzPoint).filter(Boolean);
      if (c.length < 2) return null;
      etapes.push({ type: 'pied', coords: c, limo: !!e.limo });
    } else if (e && e.type === 'metro') {
      const de = rzStation(e.de), a = rzStation(e.a);
      if (!de || !a || de === a) return null;
      etapes.push({ type: 'metro', de: de[0], a: a[0] });
    } else return null;
  }
  if (etapes[0].type !== 'pied' || etapes[etapes.length - 1].type !== 'pied') return null;
  // le trajet part bien du groupe et arrive bien a la cible
  const premier = etapes[0].coords, dernier = etapes[etapes.length - 1].coords;
  if (rzDist(premier[0], depart) > 450 || rzDist(dernier[dernier.length - 1], arrivee) > 450) return null;
  premier.unshift(depart.slice()); dernier.push(arrivee.slice());
  // les passages dans le metro commencent et finissent pres des stations
  for (let i = 0; i < etapes.length; i++) {
    const e = etapes[i]; if (e.type !== 'metro') continue;
    const avant = etapes[i - 1], apres = etapes[i + 1];
    if (!avant || !apres || avant.type !== 'pied' || apres.type !== 'pied') return null;
    e.depuis = avant.coords[avant.coords.length - 1];
    e.vers = apres.coords[0];
    const sDe = rzStation(e.de), sA = rzStation(e.a);
    if (rzDist(e.depuis, [sDe[1], sDe[2]]) > 450 || rzDist(e.vers, [sA[1], sA[2]]) > 450) return null;
    // verifier que le metro ne traverse pas un mur ennemi
    if (rzMurSurChemin(depart, [e.depuis, e.vers])) return null;
  }
  // durees
  let total = 0;
  etapes.forEach(e => {
    if (e.type === 'pied') e.duree = Math.max(rzLongueur(e.coords), rzDist(e.coords[0], e.coords[e.coords.length - 1])) / (e.limo ? RZ_V_LIMOUSINE : RZ_V_PIED);
    else e.duree = rzDist(e.depuis, e.vers) * 1.25 / RZ_V_METRO + 15;
    total += e.duree;
  });
  const f = total > RZ_DUREE_MAX ? RZ_DUREE_MAX / total : 1;
  let t = t0;
  etapes.forEach(e => { e.t0 = t; t += Math.max(1, e.duree * f) * 1000; e.t1 = Math.round(t); delete e.duree; });
  return { etapes, fin: Math.round(t) };
}
/* le chemin du retour : le meme, a l'envers */
function rzRetour(g, t0) {
  const etapes = g.etapes.slice().reverse().map(e => {
    const d = e.t1 - e.t0;
    if (e.type === 'pied') return { type: 'pied', coords: e.coords.slice().reverse(), d, limo: e.limo };
    return { type: 'metro', de: e.a, a: e.de, depuis: e.vers, vers: e.depuis, d };
  });
  let t = t0;
  etapes.forEach(e => { e.t0 = t; t += e.d; e.t1 = t; delete e.d; });
  const j = RZJ[g.proprio];
  g.etapes = etapes; g.fin = t; g.etat = 'route';
  g.cible = { type: 'maison' };
  if (j && j.base) g.cible.lon = j.base.lon, g.cible.lat = j.base.lat;
}
function rzPositionFin(g) { const e = g.etapes[g.etapes.length - 1]; return e.coords[e.coords.length - 1]; }

/* ---- a l'arrivee d'un groupe ---- */
async function rzArrivee(g) {
  const now = Date.now();
  const moi = RZJ[g.proprio];
  const c = g.cible || {};
  if (!moi) { delete RZG[g.id]; return; }

  if (c.type === 'maison') {
    RZ_TYPES.forEach(t => { moi.stock[t] += g.unites[t] | 0; });
    delete RZG[g.id];
    return;
  }
  if (c.type === 'point') { g.etat = 'poste'; g.pos = rzPositionFin(g); return; }

  if (c.type === 'poste') {
    const poste = rzPoste(c.id);
    const occupants = Object.values(RZG).filter(x => x.etat === 'poste' && x.cible && x.cible.type === 'poste' && x.cible.id === poste.id
      && x.proprio !== g.proprio && !rzAllies(g.proprio, x.proprio));
    g.etat = 'poste'; g.pos = [poste.lon, poste.lat]; g.cagnotte = 0; g.depuis = now;
    if (!occupants.length) { rzEvenement(g.proprio, 'Tes koalas ont pris le ' + poste.nom + '. Ils rapportent de l\'argent chaque minute.', 'bon'); return; }
    const def = rzVide(); occupants.forEach(o => RZ_TYPES.forEach(t => { def[t] += o.unites[t] | 0; }));
    const r = rzCombat(g.unites, 1, def, 1);
    const noms = [...new Set(occupants.map(o => RZJ[o.proprio] ? RZJ[o.proprio].pseudo : '?'))].join(', ');
    if (r.gagnant === 'A') {
      g.unites = r.A;
      occupants.forEach(o => { rzEvenement(o.proprio, moi.pseudo + ' a attaqué le ' + poste.nom + ' : tes koalas y sont tous tombés.', 'mauvais'); delete RZG[o.id]; });
      rzEvenement(g.proprio, poste.nom + ' repris à ' + noms + '. Il te reste ' + rzTotal(r.A) + ' koalas sur place.', 'bon');
    } else {
      // les survivants de la defense se repartissent entre leurs groupes
      const restes = r.B;
      occupants.forEach(o => {
        const u = rzVide();
        RZ_TYPES.forEach(t => { const pris = Math.min(o.unites[t] | 0, restes[t]); u[t] = pris; restes[t] -= pris; });
        o.unites = u;
        if (!rzTotal(u)) delete RZG[o.id];
        rzEvenement(o.proprio, moi.pseudo + ' a attaqué le ' + poste.nom + ' et a perdu. Tes koalas tiennent toujours.', 'bon');
      });
      g.unites = rzApresDefaite(g.unites);
      rzEvenement(g.proprio, 'Attaque du ' + poste.nom + ' ratée face à ' + noms + ' : tu perds 30% de tes koalas, il t\'en reste ' + rzTotal(g.unites) + ' qui rentrent à la base.', 'mauvais');
      rzRetour(g, now);
    }
    return;
  }

  if (c.type === 'mur-renfort') {
    const m = RZ_MURS[c.id];
    if (!m) { rzEvenement(g.proprio, 'Cette muraille a disparu entre-temps.', 'info'); rzRetour(g, now); return; }
    RZ_TYPES.forEach(t => { m.garnison[t] = (m.garnison[t] | 0) + (g.unites[t] | 0); });
    rzEvenement(g.proprio, rzTotal(g.unites) + ' koalas renforcent ta muraille (force désormais ' + Math.round(rzMurForce(m)) + ').', 'bon');
    delete RZG[g.id];
    return;
  }

  if (c.type === 'mur') {
    const m = RZ_MURS[c.id];
    if (!m) { rzEvenement(g.proprio, 'Cette muraille a déjà été détruite.', 'info'); rzRetour(g, now); return; }
    const D = rzMurForce(m);
    const r = rzCombat(g.unites, 1, { nu: D, pistolet: 0, diamant: 0 }, 1);
    if (r.gagnant === 'A') {
      g.unites = r.A;
      delete RZ_MURS[m.id];
      rzEvenement(m.proprio, moi.pseudo + ' a détruit une de tes murailles.', 'mauvais');
      rzEvenement(g.proprio, 'Muraille détruite. Il te reste ' + rzTotal(r.A) + ' koalas.', 'bon');
    } else {
      g.unites = rzApresDefaite(g.unites);
      rzEvenement(g.proprio, 'Attaque de la muraille ratée : tu perds 30% de tes koalas, il t\'en reste ' + rzTotal(g.unites) + ' qui rentrent à la base.', 'mauvais');
      rzEvenement(m.proprio, moi.pseudo + ' a attaqué une de tes murailles et a perdu.', 'bon');
    }
    rzRetour(g, now);
    return;
  }

  if (c.type === 'bandit') {
    const b = RZ_BANDITS.find(x => x.id === c.id);
    if (!b) { rzRetour(g, now); return; }
    rzBanditRafraichir(b, now);
    if (!rzBanditVivant(b, now)) {
      rzEvenement(g.proprio, 'Ce camp de bandits vient d\'être vaincu par quelqu\'un d\'autre : plus rien à combattre pour l\'instant.', 'info');
      rzRetour(g, now); return;
    }
    const D = RZ_BANDIT_FORCE[b.niveau - 1];
    const r = rzCombat(g.unites, 1, { nu: D, pistolet: 0, diamant: 0 }, 1);
    if (r.gagnant === 'A') {
      g.unites = r.A;
      const [mn, mx] = RZ_BANDIT_GAIN[b.niveau - 1];
      const gain = sous(mn + Math.random() * (mx - mn));
      b.mortJusqua = now + RZ_BANDIT_RESPAWN;
      await rzAjouter(g.proprio, gain);
      rzEvenement(g.proprio, 'Bandits niveau ' + b.niveau + ' vaincus : +' + gain.toLocaleString('fr-FR') + ' €. Il te reste ' + rzTotal(r.A) + ' koalas.', 'bon');
    } else {
      g.unites = rzApresDefaite(g.unites);
      rzEvenement(g.proprio, 'Attaque des bandits (niveau ' + b.niveau + ') ratée : tu perds 30% de tes koalas, il t\'en reste ' + rzTotal(g.unites) + ' qui rentrent à la base.', 'mauvais');
    }
    rzRetour(g, now);
    return;
  }

  if (c.type === 'groupe') {
    const cg = RZG[c.id];
    if (!cg || cg.proprio === g.proprio) {
      rzEvenement(g.proprio, 'Ce groupe a disparu avant que tu ne l\'atteignes.', 'info');
      rzRetour(g, now); return;
    }
    const nomCible = RZJ[cg.proprio] ? RZJ[cg.proprio].pseudo : '?';
    const r = rzCombat(g.unites, 1, cg.unites, 1);
    if (r.gagnant === 'A') {
      g.unites = r.A;
      delete RZG[cg.id];
      rzEvenement(cg.proprio, moi.pseudo + ' a attaqué ton groupe en déplacement : tes koalas sont tous tombés.', 'mauvais');
      rzEvenement(g.proprio, 'Groupe de ' + nomCible + ' détruit. Il te reste ' + rzTotal(r.A) + ' koalas.', 'bon');
    } else {
      g.unites = rzApresDefaite(g.unites);
      rzEvenement(g.proprio, 'Attaque ratée contre le groupe de ' + nomCible + ' : tu perds 30% de tes koalas, il t\'en reste ' + rzTotal(g.unites) + ' qui rentrent à la base.', 'mauvais');
      rzEvenement(cg.proprio, moi.pseudo + ' a attaqué ton groupe en déplacement et a perdu. Tes koalas tiennent toujours.', 'bon');
    }
    rzRetour(g, now);
    return;
  }

  if (c.type === 'base') {
    const cible = RZJ[c.pseudo];
    if (!cible || !cible.base) { rzRetour(g, now); return; }
    if (cible.bouclier) {
      rzEvenement(g.proprio, 'La base de ' + cible.pseudo + ' est sous bouclier : tes koalas font demi-tour.', 'info');
      rzRetour(g, now); return;
    }
    const cote = RZ_COTES.indexOf(c.cote) >= 0 ? c.cote : 'devant';
    const cotes = rzRepartir(cible.stock, cible.repartition);
    const def = cotes[cote];
    const r = rzCombat(g.unites, 1, def, rzMultDefense(cible));
    // les defenseurs tombes sont retires de la base
    RZ_TYPES.forEach(t => { cible.stock[t] = Math.max(0, cible.stock[t] - ((def[t] | 0) - (r.B[t] | 0))); });
    const nomCote = { devant: 'devant', derriere: 'derrière', gauche: 'à gauche', droite: 'à droite' }[cote];
    if (r.gagnant !== 'A') {
      g.unites = rzApresDefaite(g.unites);
      rzEvenement(g.proprio, 'Attaque ratée ' + nomCote + ' chez ' + cible.pseudo + ' : tu perds 30% de tes koalas, il t\'en reste ' + rzTotal(g.unites) + ' qui rentrent à la base.', 'mauvais');
      rzEvenement(c.pseudo, moi.pseudo + ' t\'a attaqué ' + nomCote + ' et a perdu. Il te reste ' + rzTotal(r.B) + ' défenseurs de ce côté.', 'bon');
      rzRetour(g, now);
      return;
    }
    g.unites = r.A;
    if (rzEnFeu(cible)) {
      rzEvenement(g.proprio, 'La base de ' + cible.pseudo + ' brûlait déjà : rien à piller, mais ses défenseurs ' + nomCote + ' sont tombés.', 'info');
      rzEvenement(c.pseudo, moi.pseudo + ' a tué tes défenseurs ' + nomCote + ' pendant que ta base brûlait.', 'mauvais');
      rzRetour(g, now); return;
    }
    // le pillage : 25 % du vrai solde, partage entre les allies qui attaquent la meme base
    const participants = [g.proprio];
    Object.values(RZG).forEach(x => {
      if (x.id !== g.id && x.etat === 'route' && x.cible && x.cible.type === 'base' && x.cible.pseudo === c.pseudo
          && participants.indexOf(x.proprio) < 0 && rzAllies(g.proprio, x.proprio)) participants.push(x.proprio);
    });
    cible.feuJusqua = now + RZ_FEU;
    const solde = await rzSolde(c.pseudo);
    const butin = sous(solde * RZ_PILLAGE);
    const part = sous(butin / participants.length);
    if (butin > 0) {
      await rzAjouter(c.pseudo, -butin);
      for (const p of participants) await rzAjouter(p, part);
    }
    const noms = participants.map(p => RZJ[p] ? RZJ[p].pseudo : '?').join(' et ');
    rzEvenement(c.pseudo, 'Ta base a été pillée par ' + noms + ' : −' + butin.toLocaleString('fr-FR') + ' €. Elle brûle 30 minutes.', 'mauvais');
    participants.forEach(p => rzEvenement(p, 'Pillage réussi chez ' + cible.pseudo + ' : +' + part.toLocaleString('fr-FR') + ' €' + (participants.length > 1 ? ' (partagé en ' + participants.length + ')' : '') + '. Sa base brûle.', 'bon'));
    rzRetour(g, now);
    return;
  }
  rzRetour(g, now);
}

/* ---- le battement : arrivees et revenus des postes tenus ---- */
let rzOccupe = false, rzDernierRevenu = Date.now();
setInterval(async () => {
  if (!rzCharge || rzOccupe) return;
  rzOccupe = true;
  try {
    const now = Date.now();
    const arrives = Object.values(RZG).filter(g => g.etat === 'route' && g.fin <= now).sort((a, b) => a.fin - b.fin);
    for (const g of arrives) { if (RZG[g.id] && RZG[g.id].etat === 'route') await rzArrivee(g); }
    if (arrives.length) rzSauver();
    if (now - rzDernierRevenu >= 60000) {
      rzDernierRevenu = now;
      const gains = {};
      const postesTenus = {};   // proprio -> Set des ids de postes ou il a au moins un groupe
      Object.values(RZG).forEach(g => {
        if (g.etat !== 'poste' || !g.cible || g.cible.type !== 'poste') return;
        (postesTenus[g.proprio] || (postesTenus[g.proprio] = new Set())).add(g.cible.id);
      });
      Object.values(RZG).forEach(g => {
        if (g.etat !== 'poste' || !g.cible || g.cible.type !== 'poste') return;
        const mult = rzMultControle(postesTenus[g.proprio] ? postesTenus[g.proprio].size : 1);
        g.cagnotte = (g.cagnotte || 0) + rzTotal(g.unites) * RZ_REVENU * mult;
        const verse = Math.floor(g.cagnotte * 100) / 100;
        if (verse >= 0.01) { g.cagnotte -= verse; g.gagne = sous((g.gagne || 0) + verse); gains[g.proprio] = (gains[g.proprio] || 0) + verse; }
      });
      for (const pb of Object.keys(gains)) await rzAjouter(pb, sous(gains[pb]));
      if (Object.keys(gains).length) rzSauver();
    }
  } catch (e) { console.log('Razzia : ' + e.message); }
  rzOccupe = false;
}, 1000);

/* ce que voit un joueur */
function rzVue(compte, depuis) {
  const now = Date.now();
  const pb = compte.pseudoBas;
  const moi = rzJoueur(compte);
  const bases = Object.keys(RZJ).filter(k => RZJ[k].base).map(k => {
    const j = RZJ[k];
    return { id: k, pseudo: j.pseudo, lon: j.base.lon, lat: j.base.lat, forme: j.base.forme, haut: j.base.haut,
             bouclier: !!j.bouclier, feu: rzEnFeu(j) ? j.feuJusqua : 0, allie: rzAllies(pb, k), moi: k === pb };
  });
  const groupes = Object.values(RZG).map(g => {
    const mien = g.proprio === pb;
    const o = { id: g.id, proprio: g.proprio, pseudo: RZJ[g.proprio] ? RZJ[g.proprio].pseudo : '?', mien,
                etat: g.etat, n: rzTotal(g.unites), etapes: g.etat === 'route' ? g.etapes : null, pos: g.pos || null,
                armes: RZ_TYPES.filter(t => t !== 'nu' && g.unites[t] > 0), cible: { type: g.cible.type, pseudo: g.cible.pseudo, id: g.cible.id } };
    if (mien) { o.unites = g.unites; o.cibleCote = g.cible.cote; o.gagne = g.gagne || 0; o.fin = g.fin; }
    return o;
  });
  const alertes = Object.values(RZG).filter(g => g.etat === 'route' && g.cible.type === 'base' && g.cible.pseudo === pb)
    .map(g => ({ pseudo: RZJ[g.proprio] ? RZJ[g.proprio].pseudo : '?', n: rzTotal(g.unites), fin: g.fin, cote: g.cible.cote }));
  const postes = RZ_POSTES.map(p => {
    const occ = Object.values(RZG).filter(g => g.etat === 'poste' && g.cible && g.cible.type === 'poste' && g.cible.id === p.id);
    return { id: p.id, nom: p.nom, lon: p.lon, lat: p.lat,
             occupants: [...new Set(occ.map(g => RZJ[g.proprio] ? RZJ[g.proprio].pseudo : '?'))],
             n: occ.reduce((s, g) => s + rzTotal(g.unites), 0) };
  });
  const bandits = RZ_BANDITS.map(b => {
    rzBanditRafraichir(b, now);
    return { id: b.id, lon: b.lon, lat: b.lat, niveau: b.niveau, vivant: rzBanditVivant(b, now),
             revientDans: b.mortJusqua ? Math.max(0, b.mortJusqua - now) : 0 };
  });
  const murs = Object.values(RZ_MURS).map(m => ({ id: m.id, pseudo: RZJ[m.proprio] ? RZJ[m.proprio].pseudo : '?',
    a: m.a, b: m.b, vie: Math.round(rzMurForce(m)), mien: m.proprio === pb, portail: !!m.portail, ouvert: !!m.ouvert, basculeLe: m.basculeLe || 0 }));
  const evts = moi.evenements.filter(e => e.t > (Number(depuis) || 0));
  return {
    now, solde: compte.solde, postes, bandits, murs, bases, groupes, alertes, evenements: evts,
    moi: {
      base: moi.base, deplaceUtilise: !!moi.deplaceUtilise, bouclier: moi.bouclier, bouclierDispo: moi.bouclier ? 0 : Math.max(0, moi.bouclierRetireLe + RZ_BOUCLIER_ATTENTE - now),
      feu: rzEnFeu(moi) ? moi.feuJusqua : 0, defense: moi.defense, armurerie: moi.armurerie, stock: moi.stock, limousine: !!moi.limousine,
      repartition: moi.repartition, cotes: rzRepartir(moi.stock, moi.repartition),
      allies: moi.allies.map(k => ({ id: k, pseudo: RZJ[k] ? RZJ[k].pseudo : k })),
      demandes: moi.demandes.map(k => ({ id: k, pseudo: RZJ[k] ? RZJ[k].pseudo : k })),
      groupes: rzGroupesDe(pb).length
    },
    regles: { prix: RZ_PRIX, force: RZ_FORCE, niveauArme: RZ_NIV_ARME, prixArmurerie: RZ_PRIX_ARMURERIE,
              armurerieMax: RZ_ARMURERIE_MAX, prixDefense: RZ_PRIX_DEFENSE, maxGroupes: RZ_MAX_GROUPES, reparation: RZ_REPARATION,
              stations: RZ_STATIONS, zone: RZ_ZONE, banditForce: RZ_BANDIT_FORCE, banditGain: RZ_BANDIT_GAIN,
              murCout: RZ_MUR_COUT, murRembours: RZ_MUR_REMBOURS, murLongueurMin: RZ_MUR_LONGUEUR_MIN, murLongueurMax: RZ_MUR_LONGUEUR_MAX, murChaineMax: RZ_MUR_CHAINE_MAX,
              portailCout: RZ_PORTAIL_COUT, prixLimousine: RZ_PRIX_LIMOUSINE }
  };
}

const serveur = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://x');
  const route = url.pathname;

  /* ---------------- API ---------------- */
  if (route.startsWith('/api/')) {

    // --- creer un compte ---
    if (route === '/api/inscription' && req.method === 'POST') {
      const body   = await corpsJSON(req);
      const pseudo = String(body.pseudo || '').trim().slice(0, 16);
      const mdp    = String(body.motDePasse || '');
      const email  = String(body.email || '').trim().toLowerCase();

      if (pseudo.length < 3) {
        return repondre(res, 400, { erreur: 'Choisissez un pseudo d\'au moins 3 caracteres.' });
      }
      if (!/^[\p{L}\p{N} _.'-]+$/u.test(pseudo)) {
        return repondre(res, 400, { erreur: 'Pseudo : lettres, chiffres et espaces uniquement.' });
      }
      if (mdp.length < 4) {
        return repondre(res, 400, { erreur: 'Mot de passe trop court (4 caracteres minimum).' });
      }
      if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email)) {
        return repondre(res, 400, { erreur: 'Email invalide.' });
      }

      const pseudoBas = pseudo.toLowerCase();
      if (await Carnet.lire(pseudoBas)) {
        return repondre(res, 409, { erreur: 'Ce pseudo est deja pris. Choisissez-en un autre.' });
      }

      // Generer un code de verification 6 chiffres
      const code = String(crypto.randomInt(100000, 999999));
      const expire = Date.now() + 10 * 60 * 1000;  // expire dans 10 minutes

      // Stocker temporairement le code et les donnees d\'inscription
      codesVerification.set(pseudoBas, {
        code,
        email,
        pseudo,
        mdp,
        expire
      });

      // Envoyer l\'email
      const envoye = await envoyerEmailVerification(email, pseudo, code);
      /* l'email n'a pas pu partir (envoi bloque par l'hebergeur) : on ne bloque
         pas le joueur, la page valide elle-meme l'inscription tout de suite */
      if (!envoye) {
        return repondre(res, 200, { pseudo: pseudo, sansEmail: true, code: code });
      }

      return repondre(res, 200, {
        message: 'Code de verification envoye. Verifiez votre email.',
        pseudo: pseudo
      });
    }

    // --- verifier le code email et creer le compte ---
    if (route === '/api/verifier-email' && req.method === 'POST') {
      const body   = await corpsJSON(req);
      const pseudo = String(body.pseudo || '').trim();
      const code   = String(body.code || '').trim();

      if (!pseudo || !code) {
        return repondre(res, 400, { erreur: 'Pseudo et code requis.' });
      }

      const pseudoBas = pseudo.toLowerCase();
      const data = codesVerification.get(pseudoBas);

      if (!data) {
        return repondre(res, 400, { erreur: 'Aucune inscription en attente pour ce pseudo.' });
      }

      if (data.expire < Date.now()) {
        codesVerification.delete(pseudoBas);
        return repondre(res, 400, { erreur: 'Code expire. Recommencez l\'inscription.' });
      }

      if (data.code !== code) {
        return repondre(res, 400, { erreur: 'Code incorrect.' });
      }

      // Code valide : creer le compte
      const fiche = {
        pseudoBas,
        pseudo: data.pseudo,
        email: data.email,
        motDePasse: await chiffrer(data.mdp),
        solde: SOLDE_DEPART,
        mains: 0, gagnees: 0, perdues: 0, poissons: 0,
        penaltys: 0, buts: 0, defaitesPenalty: 0, periphs: 0, portes: 0, periph: null, perso: null,
        voiturePremium: false, codesUtilises: [], tower: null, tours: 0, banni: false,
        emailVerifie: true
      };

      if (!await Carnet.creer(fiche)) {
        return repondre(res, 409, { erreur: 'Ce pseudo est deja pris. Recommencez l\'inscription.' });
      }

      codesVerification.delete(pseudoBas);
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
      if (fiche.banni) return repondre(res, 403, { erreur: 'Ce compte a ete banni du casino.' });
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
    // un compte banni ne peut plus rien faire, meme avec une session encore ouverte
    if (compte.banni) return repondre(res, 403, { erreur: 'Ce compte a ete banni du casino.' });

    // --- liste des tables ---
    if (route === '/api/salon') {
      return repondre(res, 200, { tables: resumeSalon(), roulette: resumeRoulette(), solde: compte.solde });
    }

    // --- s\'asseoir ---
    if (route === '/api/asseoir' && req.method === 'POST') {
      const table = trouverTable(String(body.table || ''));
      if (!table) return repondre(res, 404, { erreur: 'table inconnue' });

      // on quitte l\'ancienne table le cas echeant
      quitterTable(compte);

      if (table.jeu === 'poker') {
        // une place vraiment libre (pas celle d\'un joueur parti en pleine donne)
        const fantome = i => !!(table.main && table.phase !== 'attente' && table.phase !== 'decompte' &&
                                table.main.joueurs[i]);
        const place = table.places.findIndex((p, i) => !p && !fantome(i));
        if (place < 0) return repondre(res, 409, { erreur: 'table complete' });
        table.places[place] = {
          type: 'humain', jeton: compte.jetonRef, nom: compte.pseudo,
          solde: compte.solde, soldeVisible: !!compte.soldeVisible
        };
        compte.table = table.id;
        compte.siege = place;
        touche(table);
        return repondre(res, 200, etatPour(table, compte.jetonRef));
      }

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

    // --- s\'asseoir a la table de roulette ---
    if (route === '/api/roulette-asseoir' && req.method === 'POST') {
      // deja assis : on renvoie simplement l\'etat
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
      if (table.jeu === 'poker') return repondre(res, 409, { erreur: 'pas au poker' });
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

      if (table.jeu === 'poker') {
        const m = table.main;
        if (table.phase !== 'parole' || !m || m.actif !== monIndex) {
          return repondre(res, 409, { erreur: 'pas votre tour' });
        }
        const action = String(body.action || '');
        if (!['coucher', 'checker', 'suivre', 'relancer', 'tapis'].includes(action)) {
          return repondre(res, 400, { erreur: 'action inconnue' });
        }
        let to;
        if (action === 'relancer') {
          const v = Number(body.montant);          // montant TOTAL de la mise apres relance, en euros
          if (!isFinite(v) || v <= 0) return repondre(res, 400, { erreur: 'montant invalide' });
          to = cts(v);
        }
        pkAgir(table, monIndex, { type: action, to });
        return repondre(res, 200, etatPour(table, compte.jetonRef));
      }

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

    // --- offrir de l\'argent a un joueur assis a la meme table ---
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
      // permet au destinataire (et a lui seul) d\'afficher une notification
      table.chat.push({
        id: ++table.chatId, systeme: true,
        texte: p.nom + ' offre ' + eur(v) + ' a ' + cible.nom + '.', t: Date.now(),
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

    // --- chat de table (ephemere : voir cote client pour l\'affichage) ---
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

    // --- une prise a la peche : c\'est le serveur qui credite ---
    if (route === '/api/peche' && req.method === 'POST') {
      compte.solde    = sous(compte.solde + 1);
      compte.poissons = compte.poissons + 1;
      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
      Carnet.enregistrer(compte);
      return repondre(res, 200, { solde: compte.solde, poissons: compte.poissons });
    }

    // --- l\'apparence du personnage ---
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
        return repondre(res, 409, { erreur: 'Une serie est deja en cours.' });
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
      if (!serie) return repondre(res, 409, { erreur: 'Aucune serie en cours.' });

      const zone = Math.max(0, Math.min(ZONES_PENALTY - 1, Number(body.zone) | 0));

      /* Le petit secret : apres deux echecs d\'affilee, viser la tete du
         gardien donne un but a coup sur. C\'est le serveur qui verifie la
         condition, pas la page : impossible de s\'en servir a volonte. */
      const viseLaTete = body.tete === true;
      const secret = viseLaTete && (compte.defaitesPenalty | 0) >= DEFAITES_SECRET;

      // le sort en est jete
      const but = secret || crypto.randomInt(10000) < CHANCE_BUT;

      // le gardien plonge la ou il faut pour que l\'image colle au resultat
      let zoneGardien;
      if (secret)   zoneGardien = -1;          // il ne bouge pas, il encaisse
      else if (but) { do { zoneGardien = crypto.randomInt(ZONES_PENALTY); } while (zoneGardien === zone); }
      else          zoneGardien = zone;

      compte.penaltys = compte.penaltys + 1;

      if (!but) {
        // rate : la mise est perdue, la serie s\'arrete
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

      // but : on monte d\'un cran
      compte.buts = compte.buts + 1;
      compte.defaitesPenalty = 0;
      serie.palier = serie.palier + 1;
      const multiplicateur = ECHELLE_PENALTY[serie.palier - 1];
      const gainPotentiel  = sous(serie.mise * multiplicateur);
      const auSommet       = serie.palier >= ECHELLE_PENALTY.length;

      if (auSommet) {
        // au sommet de l\'echelle, on encaisse d\'office
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

    // --- on encaisse et on s\'arrete la ---
    if (route === '/api/penalty-encaisser' && req.method === 'POST') {
      const serie = compte.penalty;
      if (!serie) return repondre(res, 409, { erreur: 'Aucune serie en cours.' });
      if (serie.palier < 1) {
        return repondre(res, 400, { erreur: 'Marquez au moins un but avant d\'encaisser.' });
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
      if (compte.bois) abandonnerBois(compte);
      const voiture = demarrerCourseInterne(compte, mise, body.voiture);

      return repondre(res, 200, {
        ok: true, mise: mise, palier: 0, solde: compte.solde, voiture: voiture,
        echelle: ECHELLE_PERIPH, longueurs: LONGUEURS_PERIPH
      });
    }

    // --- la boutique : on achete la voiture premium ---
    if (route === '/api/periph-acheter-voiture' && req.method === 'POST') {
      if (compte.voiturePremium) {
        return repondre(res, 409, { erreur: 'Vous avez deja cette voiture.' });
      }
      if (compte.periph) {
        return repondre(res, 409, { erreur: 'Terminez votre course avant d\'aller a la boutique.' });
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
        return repondre(res, 409, { erreur: 'Course deja terminee.' });
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

      // pour l\'affichage de la voiture des autres joueurs reels (multijoueur uniquement)
      majGroupeCoursePeriph(compte, { palier: suivant, fraction: 0, statut: fini ? 'arrive' : 'course' });

      if (fini) {                                   // Saint-Denis : on encaisse d\'office
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

    // --- la voiture est detruite, ou on s\'est fait doubler ---
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
       Une vraie file d\'attente : le depart n\'a lieu que si un deuxieme
       joueur reel rejoint. Le gain/la perte de chacun reste toujours
       gouverne par les routes ci-dessus, inchangees.
       =============================================================== */

    // --- on rejoint la file d\'attente ---
    if (route === '/api/periph-multi-rejoindre' && req.method === 'POST') {
      /* on ne peut appuyer sur "Multijoueur" que depuis l\'accueil du jeu : une
         course encore ouverte ici a donc ete abandonnee (page rechargee, onglet
         ferme en pleine course). Elle est perdue, exactement comme en solo
         (/api/periph-demarrer), au lieu de bloquer le multijoueur pour toujours. */
      if (compte.periphMulti) {
        majGroupeCoursePeriph(compte, { statut: 'crash' });
        compte.periphMulti = null;
      }
      if (compte.periph) { compte.periph = null; Carnet.enregistrer(compte); }
      if (compte.bois) abandonnerBois(compte);
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

    // --- on quitte la file d\'attente (bouton ou changement d\'avis) ---
    if (route === '/api/periph-multi-quitter' && req.method === 'POST') {
      retirerDeLaFilePeriph(compte.jetonRef);
      return repondre(res, 200, { ok: true });
    }

    // --- etat de la file / du compte a rebours (appele en boucle) ---
    if (route === '/api/periph-multi-etat') {
      if (compte.periphMulti && groupesCoursePeriph.has(compte.periphMulti.groupeId)) {
        return repondre(res, 200, {
          statut: 'parti',
          /* depuis combien de temps la course est partie ici : chaque page cale
             son "3, 2, 1, GO" sur ce meme instant, au lieu de partir quand son
             propre sondage (toutes les 700 ms, plus le reseau) s\'en apercoit */
          ecoule: Date.now() - groupesCoursePeriph.get(compte.periphMulti.groupeId).creeLe,
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
        const m = g.membres[compte.jetonRef];
        m.fraction = Math.max(0, Math.min(1, Number(body.fraction) || 0));
        m.x = Math.max(-7, Math.min(7, Number(body.x) || 0));
        /* position absolue (metres depuis la Porte Dauphine) et vitesse (km/h) :
           c\'est ce que les autres pages dessinent. Avant, seule la fraction du
           troncon etait envoyee, et elle etait recombinee ici avec le palier du
           serveur, qui retarde sur celui de la page : la voiture sautait.
           Ca ne sert qu\'a l\'affichage, jamais a un gain ; on borne quand meme
           a ce qui est physiquement possible depuis le depart. */
        if (body.d !== undefined) {
          const course = compte.periph;
          const vmax = course && course.voiture === VOITURE_PREMIUM_INDICE ? VITESSE_MAX_PERIPH_PREMIUM : VITESSE_MAX_PERIPH;
          const possible = course ? (Date.now() - course.depart) / 1000 * vmax + 30 : Infinity;
          m.d = Math.max(0, Math.min(distancePeriph(ECHELLE_PERIPH.length), possible, Number(body.d) || 0));
          m.v = Math.max(0, Math.min(300, Number(body.v) || 0));
          /* l\'instant de la mesure : a son arrivee ici, moins le trajet aller
             annonce par la page (la moitie de son aller-retour mesure). Les
             autres pages savent ainsi exactement de quand date la position,
             et la prolongent du bon temps (voir majVoitureReelle). La porte
             franchie (/api/periph-porte) touche "maj" mais pas ceci. */
          const trajet = Math.max(0, Math.min(1500, Number(body.lat) || 0));
          m.mesure = Date.now() - trajet;
        }
        m.maj = Date.now();
      }
      // on renvoie tout de suite la position des autres : un seul aller-retour par echange
      return repondre(res, 200, { ok: true, membres: autresMembresPeriph(compte), t: Date.now() });
    }

    // --- on recupere la progression des autres joueurs reels de la course ---
    if (route === '/api/periph-multi-course') {
      return repondre(res, 200, { membres: autresMembresPeriph(compte), t: Date.now() });
    }

    /* ===============================================================
       LE BOIS DE BOULOGNE (sortie a droite de la Porte Dauphine)
       =============================================================== */

    // --- on tourne a droite : la mise du periph passe dans la poursuite ---
    if (route === '/api/bois-sortir' && req.method === 'POST') {
      const course = compte.periph;
      if (!course) return repondre(res, 409, { erreur: 'Aucune course en cours.' });
      if (course.palier !== 0) return repondre(res, 409, { erreur: 'La sortie du bois est passee.' });
      const vitesseMax = course.voiture === VOITURE_PREMIUM_INDICE ? VITESSE_MAX_PERIPH_PREMIUM : VITESSE_MAX_PERIPH;
      if ((Date.now() - course.depart) / 1000 < BOIS_SORTIE_MIN / vitesseMax * MARGE_TEMPS) {
        return repondre(res, 400, { erreur: 'Course invalide.' });
      }
      if (compte.bois) abandonnerBois(compte);
      compte.bois = { mise: course.mise, voiture: course.voiture, groupeId: null, slot: 0, balles: 0 };
      compte.periph = null;
      majGroupeCoursePeriph(compte, { statut: 'bois' });
      compte.periphMulti = null;
      fileBois.push(compte.jetonRef);
      let f = formationsBois.find(x => x.jetons.length < BOIS_MAX);
      if (!f) { f = { echeance: Date.now() + BOIS_ATTENTE, jetons: [] }; formationsBois.push(f); }
      f.jetons.push(compte.jetonRef);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, secondes: Math.ceil((f.echeance - Date.now()) / 1000) });
    }

    // --- le decompte, puis le depart (appele en boucle) ---
    if (route === '/api/bois-etat') {
      const g = groupeBoisDe(compte);
      if (g) {
        return repondre(res, 200, Object.assign({ statut: 'parti', graine: g.graine,
          slot: compte.bois.slot, depuis: BOIS_DEPART_POLICE,
          equipe: Object.values(g.membres).map(m => ({ slot: m.slot, pseudo: m.pseudo, voiture: m.voiture })) },
          etatBoisPour(compte, g), { statut: 'parti' }));
      }
      const f = formationBoisDe(compte.jetonRef);
      if (f && compte.bois) {
        return repondre(res, 200, { statut: 'compteADebours',
          secondes: Math.max(0, Math.ceil((f.echeance - Date.now()) / 1000)),
          joueurs: f.jetons.map(j => { const c = comptes.get(j); return c ? c.pseudo : '?'; }) });
      }
      return repondre(res, 200, { statut: 'aucune' });
    }

    // --- on annonce sa position ; on recoit celle des autres et la vie de Toledo ---
    if (route === '/api/bois-progres' && req.method === 'POST') {
      const g = groupeBoisDe(compte);
      if (!g) return repondre(res, 409, { erreur: 'pas en course' });
      const m = g.membres[compte.jetonRef];
      if (m && m.statut === 'course') {
        const now = Date.now();
        const possible = Math.max(0, now - g.depart - BOIS_DEPART_POLICE) / 1000 * BOIS_VITESSE_MAX + 30;
        m.d = Math.max(0, Math.min(possible, Number(body.d) || 0));
        m.x = Math.max(-7, Math.min(7, Number(body.x) || 0));
        m.v = Math.max(0, Math.min(330, Number(body.v) || 0));
        m.mesure = now - Math.max(0, Math.min(1500, Number(body.lat) || 0));
        m.maj = now;
      }
      return repondre(res, 200, etatBoisPour(compte, g));
    }

    // --- on ramasse une caisse : le serveur dit ce qu'il y a dedans ---
    if (route === '/api/bois-ramasser' && req.method === 'POST') {
      const g = groupeBoisDe(compte);
      if (!g || g.statut !== 'course') return repondre(res, 409, { erreur: 'pas en course' });
      const m = g.membres[compte.jetonRef];
      const i = Number(body.i) | 0;
      const o = g.plan.objets[i];
      if (!m || m.statut !== 'course' || !o) return repondre(res, 400, { erreur: 'objet inconnu' });
      if (g.pris.indexOf(i) >= 0) return repondre(res, 200, { ok: false, pris: g.pris });
      const d = Number(body.d) || 0, x = Number(body.x) || 0;
      if (Math.abs(d - o.d) > 10 || Math.abs(x - o.x) > 2.8 || Math.abs(d - dBoisEstimee(m, Date.now())) > 45) {
        return repondre(res, 200, { ok: false, pris: g.pris });
      }
      g.pris.push(i);
      if (o.genre === 'pistolet') compte.bois.balles = BOIS_BALLES;
      compte.bois.objet = o.genre;
      return repondre(res, 200, { ok: true, genre: o.genre, balles: compte.bois.balles, pris: g.pris });
    }

    // --- un coup sur Toledo (choc ou balle) : verifie contre son trajet ---
    if (route === '/api/bois-coup' && req.method === 'POST') {
      const g = groupeBoisDe(compte);
      if (!g) return repondre(res, 409, { erreur: 'pas en course' });
      const m = g.membres[compte.jetonRef];
      const now = Date.now();
      let touche = false;
      if (g.statut === 'course' && m && m.statut === 'course') {
        const ecoule = now - g.depart;
        const tc = Number(body.tc) || 0;
        const d = Number(body.d) || 0, x = Number(body.x) || 0;
        const plausible = tc >= ecoule - 1500 && tc <= ecoule + 400 && tc >= BOIS_DEPART_POLICE
          && Math.abs(d - dBoisEstimee(m, now)) < 40;
        const T = etatToledo(g.plan, tc, g.boosts);
        if (body.type === 'balle') {
          if (compte.bois.balles > 0 && now - m.dernierTir > 180) {
            compte.bois.balles--; m.dernierTir = now;
            const devant = (T.d + 2.3) - (d + 3);
            if (plausible && devant > -1 && devant < 62 && Math.abs(x - T.x) < 1.7) {
              g.vie = Math.max(0, g.vie - BOIS_DEGAT_BALLE); touche = true;
            }
          }
        } else if (now - m.dernierChoc > 450) {
          if (plausible && Math.abs((d + 1.5) - (T.d + 2.3)) < 5.8 && Math.abs(x - T.x) < 2.7) {
            m.dernierChoc = now;
            g.vie = Math.max(0, g.vie - BOIS_DEGAT_CHOC); touche = true;
          }
        }
        /* chaque quart de vie perdu : il remet un gros coup d'accélérateur */
        while (g.vie > 0 && g.vie <= g.seuil && g.seuil > 0) {
          g.boosts.push({ t: ecoule + 150, dur: 2600, dv: 75 });
          g.seuil -= g.vieMax / 4;
        }
        if (g.vie <= 0) gagnerBois(g);
      }
      return repondre(res, 200, Object.assign({ ok: true, touche }, etatBoisPour(compte, g)));
    }

    // --- la voiture de police est detruite : hors course, la mise est perdue ---
    if (route === '/api/bois-perdu' && req.method === 'POST') {
      const k = fileBois.indexOf(compte.jetonRef); if (k >= 0) fileBois.splice(k, 1);
      abandonnerBois(compte);
      return repondre(res, 200, { ok: true, solde: compte.solde });
    }

    /* ===============================================================
       LE PONT DE CRISTAL - SOLO
       ---------------------------------------------------------------
       Le pont est tire ici au depart et ne quitte jamais le serveur :
       la page apprend seulement, rangee par rangee, si la vitre choisie
       a tenu (et, une fois la rangee jouee, ou etait la bonne).
       =============================================================== */
    if (route === '/api/pont-demarrer' && req.method === 'POST') {
      if (compte.pont) return repondre(res, 409, { erreur: 'Une traversee est deja en cours.' });
      const g = salonPontDe(compte);
      if (g && g.membres[compte.jetonRef] && g.membres[compte.jetonRef].statut === 'jeu') {
        return repondre(res, 409, { erreur: 'Une traversee multijoueur est en cours.' });
      }
      const nomMode = MODES_PONT[body.mode] ? body.mode : 'classique';
      const m = MODES_PONT[nomMode];
      const mise = sous(Number(body.mise) || 0);
      if (!(mise >= MISE_MINI_PONT)) return repondre(res, 400, { erreur: 'Mise minimum : 0,10 €.' });
      if (mise > MISE_MAXI_PONT)     return repondre(res, 400, { erreur: 'Mise maximum : 200 €.' });
      if (mise > compte.solde)       return repondre(res, 400, { erreur: 'Solde insuffisant.' });

      compte.solde = sous(compte.solde - mise);
      compte.pont = { mode: nomMode, mise: mise, rangs: tirerPont(m), pos: 0 };
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, mise: mise, mode: nomMode, rangees: m.rangees, largeur: m.largeur, solde: compte.solde });
    }

    if (route === '/api/pont-avancer' && req.method === 'POST') {
      const p = compte.pont;
      if (!p) return repondre(res, 409, { erreur: 'Aucune traversee en cours.' });
      const m = MODES_PONT[p.mode];
      const j = Number(body.vitre) | 0;
      if (j < 0 || j >= m.largeur) return repondre(res, 400, { erreur: 'Vitre inconnue.' });
      const k = p.pos + 1, rang = p.rangs[k - 1];
      if (!rang[j]) {
        compte.pont = null;
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, tient: false, rangee: k, solides: rang, perdu: p.mise, solde: compte.solde });
      }
      p.pos = k;
      const mult = m.solo[k - 1];
      if (k >= m.rangees) {                       // la rive d\'or : on encaisse d\'office
        const gain = sous(p.mise * mult);
        compte.solde = sous(compte.solde + gain);
        compte.pont = null;
        soldeAuSiege(compte);
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, tient: true, rangee: k, solides: rang, complete: true, mult: mult, gain: gain, solde: compte.solde });
      }
      return repondre(res, 200, { ok: true, tient: true, rangee: k, solides: rang, mult: mult, solde: compte.solde });
    }

    if (route === '/api/pont-encaisser' && req.method === 'POST') {
      const p = compte.pont;
      if (!p) return repondre(res, 409, { erreur: 'Aucune traversee en cours.' });
      if (p.pos < 1) return repondre(res, 400, { erreur: 'Franchissez au moins une rangee avant d\'encaisser.' });
      const mult = MODES_PONT[p.mode].solo[p.pos - 1];
      const gain = sous(p.mise * mult);
      compte.solde = sous(compte.solde + gain);
      compte.pont = null;
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, gain: gain, mult: mult, rangee: p.pos, solde: compte.solde });
    }

    // on quitte en pleine traversee : la mise reste perdue, comme a Tower Rush
    if (route === '/api/pont-abandonner' && req.method === 'POST') {
      compte.pont = null;
      return repondre(res, 200, { ok: true });
    }

    /* ===============================================================
       LE PONT DE CRISTAL - MULTIJOUEUR
       ---------------------------------------------------------------
       Meme file d\'attente que le periph (2e joueur -> 10 s -> depart,
       3 joueurs au plus). Pas de tour de role : chacun avance quand il
       veut sur le MEME pont. Toute rangee foulee par l\'un (vitre qui
       tient ou qui casse) devient connue de tout le salon.
       =============================================================== */
    if (route === '/api/pont-multi-rejoindre' && req.method === 'POST') {
      if (compte.pontMulti) abandonnerPontMulti(compte);
      if (compte.pont) compte.pont = null;
      if (filePontMulti.some(e => e.jeton === compte.jetonRef)) return repondre(res, 200, { ok: true });
      const mise = sous(Number(body.mise) || 0);
      if (!(mise >= MISE_MINI_PONT)) return repondre(res, 400, { erreur: 'Mise minimum : 0,10 €.' });
      if (mise > MISE_MAXI_PONT)     return repondre(res, 400, { erreur: 'Mise maximum : 200 €.' });
      if (mise > compte.solde)       return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      compte.pontMultiErreur = null;
      filePontMulti.push({ jeton: compte.jetonRef, pseudo: compte.pseudo, mise: mise, rejointLe: Date.now() });
      return repondre(res, 200, { ok: true });
    }

    if (route === '/api/pont-multi-quitter' && req.method === 'POST') {
      retirerDeLaFilePont(compte.jetonRef);
      if (compte.pontMulti) abandonnerPontMulti(compte);
      return repondre(res, 200, { ok: true });
    }

    if (route === '/api/pont-multi-etat') {
      const g = salonPontDe(compte);
      if (g) return repondre(res, 200, vuePontMulti(compte, g));
      if (compte.pontMulti) compte.pontMulti = null;      // salon expire
      if (filePontMulti.some(e => e.jeton === compte.jetonRef)) {
        const f = groupeEnFormationPont;
        if (f && f.jetons.indexOf(compte.jetonRef) >= 0) {
          return repondre(res, 200, { statut: 'compteADebours',
            secondes: Math.max(0, Math.ceil((f.echeance - Date.now()) / 1000)), effectif: f.jetons.length });
        }
        return repondre(res, 200, { statut: 'attente' });
      }
      if (compte.pontMultiErreur) {
        const erreur = compte.pontMultiErreur;
        compte.pontMultiErreur = null;
        return repondre(res, 200, { statut: 'erreur', erreur: erreur });
      }
      return repondre(res, 200, { statut: 'aucune' });
    }

    if (route === '/api/pont-multi-avancer' && req.method === 'POST') {
      const g = salonPontDe(compte);
      const moi = g && g.membres[compte.jetonRef];
      if (!moi || moi.statut !== 'jeu') return repondre(res, 409, { erreur: 'Aucune traversee en cours.' });
      const m = MODES_PONT.classique;
      const j = Number(body.vitre) | 0;
      if (j < 0 || j >= m.largeur) return repondre(res, 400, { erreur: 'Vitre inconnue.' });
      const k = moi.pos + 1, rang = g.rangs[k - 1];
      g.revele[k - 1] = rang.indexOf(true);           // desormais connue de tout le salon
      moi.pos = k; moi.vitre = j; moi.maj = Date.now();
      if (!rang[j]) {
        moi.statut = 'tombe';
        if (g.casses[k - 1].indexOf(j) < 0) g.casses[k - 1].push(j);
        Carnet.enregistrer(compte);
        return repondre(res, 200, Object.assign(vuePontMulti(compte, g),
          { ok: true, tient: false, rangee: k, perdu: moi.mise }));
      }
      const mult = m.duo[k - 1];
      if (k >= m.rangees) {
        moi.gain = sous(moi.mise * mult);
        moi.statut = 'arrive';
        compte.solde = sous(compte.solde + moi.gain);
        soldeAuSiege(compte);
        Carnet.enregistrer(compte);
        return repondre(res, 200, Object.assign(vuePontMulti(compte, g),
          { ok: true, tient: true, rangee: k, complete: true, mult: mult, gain: moi.gain }));
      }
      return repondre(res, 200, Object.assign(vuePontMulti(compte, g), { ok: true, tient: true, rangee: k, mult: mult }));
    }

    if (route === '/api/pont-multi-encaisser' && req.method === 'POST') {
      const g = salonPontDe(compte);
      const moi = g && g.membres[compte.jetonRef];
      if (!moi || moi.statut !== 'jeu') return repondre(res, 409, { erreur: 'Aucune traversee en cours.' });
      if (moi.pos < 1) return repondre(res, 400, { erreur: 'Franchissez au moins une rangee avant d\'encaisser.' });
      const mult = MODES_PONT.classique.duo[moi.pos - 1];
      moi.gain = sous(moi.mise * mult);
      moi.statut = 'encaisse'; moi.maj = Date.now();
      compte.solde = sous(compte.solde + moi.gain);
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, Object.assign(vuePontMulti(compte, g), { ok: true, gain: moi.gain, mult: mult, rangee: moi.pos }));
    }

    /* ===============================================================
       TOWER RUSH
       ---------------------------------------------------------------
       Le seul chiffre que la page choisit vraiment, c\'est le moment ou
       elle demande le lacher. Tout le reste (l\'instant exact ou ca en
       etait dans le balancement, la precision qui en decoule, le
       multiplicateur tire, le risque d\'effondrement) est recalcule ici
       a partir de l\'heure d\'arrivee de la requete. Personne ne peut
       forcer un bon multiplicateur en trafiquant la page.
       =============================================================== */

    // --- on pose sa mise, le premier etage commence a se balancer ---
    if (route === '/api/tower-demarrer' && req.method === 'POST') {
      if (compte.tower) return repondre(res, 409, { erreur: 'Une tour est deja en cours.' });
      const mise = sous(Number(body.mise) || 0);
      if (!(mise >= MISE_MINI_TOWER)) return repondre(res, 400, { erreur: 'Mise minimum : 0,10 €.' });
      if (mise > MISE_MAXI_TOWER)     return repondre(res, 400, { erreur: 'Mise maximum : 500 €.' });
      if (mise > compte.solde)        return repondre(res, 400, { erreur: 'Solde insuffisant.' });

      compte.solde = sous(compte.solde - mise);
      compte.tower = {
        mise: mise, floors: [], leanSum: 0, visOffset: 0, frozenLeft: 0, niveau: 0,
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
      const r = towerTirer(tour, amp * Math.sin(2 * Math.PI * ecoule / period));

      if (r.issue === 'rate') {
        const perdu = tour.mise;
        compte.tower = null;
        Carnet.enregistrer(compte);
        return repondre(res, 200, {
          ok: true, rate: true, angle: r.angle, perdu: perdu, solde: compte.solde
        });
      }

      // le sommet (niveau TOWER_NIVEAUX, ou le plafond TOWER_MULT_MAX) : on encaisse d\'office
      if (r.sommet) {
        const gain = sous(tour.mise * tour.totalMult);
        compte.solde = sous(compte.solde + gain);
        compte.tower = null;
        const info = siegeDe(compte);
        if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
        Carnet.enregistrer(compte);
        return repondre(res, 200, {
          ok: true, rate: false, glisse: false, facteur: r.facteur, parfait: r.parfait,
          lean: tour.visOffset, totalMult: tour.totalMult, sommet: true, gain: gain,
          niveau: tour.niveau, niveaux: TOWER_NIVEAUX, solde: compte.solde
        });
      }

      tour.swingStart = Date.now();
      Carnet.enregistrer(compte);
      return repondre(res, 200, {
        ok: true, rate: false, glisse: false, facteur: r.facteur, parfait: r.parfait,
        lean: tour.visOffset, totalMult: tour.totalMult, solde: compte.solde,
        gele: tour.frozenLeft > 0, niveau: tour.niveau, niveaux: TOWER_NIVEAUX,
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
      if (tour.floors.length < 1) return repondre(res, 400, { erreur: 'Posez au moins un etage avant d\'encaisser.' });

      const gain = sous(tour.mise * Math.min(TOWER_MULT_MAX, tour.totalMult));   // plafond dur x100
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
       site. On accepte l\'espace, le signe € et "eur"/"euros" en trop,
       parce que c\'est malcommode a taper sur un telephone.
       =============================================================== */
    if (route === '/api/code' && req.method === 'POST') {
      // --- frein contre le devinage en boucle (un script qui essaie plein
      // de codes d\'affilee) : 5 essais rates maximum par minute et par
      // compte, ensuite on refuse sans meme regarder le code envoye. ---
      const maintenantCode = Date.now();
      if (!Array.isArray(compte.codeEchecs)) compte.codeEchecs = [];
      compte.codeEchecs = compte.codeEchecs.filter(t => maintenantCode - t < 60000);
      if (compte.codeEchecs.length >= 5) {
        return repondre(res, 429, { erreur: 'Trop d\'essais. Reessayez dans une minute.' });
      }

      let normalise = String(body.code || '').trim().toLowerCase()
        .replace(/\s+/g, '').replace(/[''']/g, '').replace(/€/g, '')
        .replace(/(euros|euro|eur)$/, '');

      if (normalise === '50') {
        if (!Array.isArray(compte.codesUtilises)) compte.codesUtilises = [];
        if (compte.codesUtilises.indexOf('50EUROS') >= 0) {
          return repondre(res, 409, { erreur: 'Ce code a deja ete utilise.' });
        }
        compte.codesUtilises.push('50EUROS');
        compte.solde = sous(compte.solde + 50);
        const info = siegeDe(compte);
        if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, genre: 'credit', solde: compte.solde });
      }

      // Codes reserves au proprietaire du site. Change-les si tu penses que
      // quelqu\'un d\'autre les connait : c\'est la seule protection, donc ils
      // ne doivent JAMAIS apparaitre dans index.html, ni dans un fichier
      // partage avec quelqu\'un d\'autre, ni etre dits a voix haute.
      if (normalise === 'martins') {                 // liste des comptes, lecture seule
        const liste = await Carnet.listerJoueurs();
        return repondre(res, 200, { ok: true, genre: 'liste', joueurs: listeJoueursAvecPresence(liste) });
      }
      if (normalise === 'exclusionfdp') {             // meme liste, avec le pouvoir de bannir
        const liste = await Carnet.listerJoueurs();
        const joueurs = listeJoueursAvecPresence(liste);
        for (const j of joueurs) {
          const fiche = await Carnet.lire(j.pseudoBas);
          j.banni = !!(fiche && fiche.banni);
          j.solde = fiche ? Number(fiche.solde || 0) : 0;
        }
        return repondre(res, 200, { ok: true, genre: 'admin', joueurs });
      }

      compte.codeEchecs.push(maintenantCode);
      return repondre(res, 400, { erreur: 'Code invalide.' });
    }

    // --- bannir / debannir un compte : protege par le meme code que la
    // liste admin, verifie a chaque appel (pas de session admin a part). ---
    if (route === '/api/bannir' && req.method === 'POST') {
      const maintenantBan = Date.now();
      if (!Array.isArray(compte.codeEchecs)) compte.codeEchecs = [];
      compte.codeEchecs = compte.codeEchecs.filter(t => maintenantBan - t < 60000);
      if (compte.codeEchecs.length >= 5) {
        return repondre(res, 429, { erreur: 'Trop d\'essais. Reessayez dans une minute.' });
      }
      const codeNorm = String(body.code || '').trim().toLowerCase()
        .replace(/\s+/g, '').replace(/[''']/g, '');
      if (codeNorm !== 'exclusionfdp') {
        compte.codeEchecs.push(maintenantBan);
        return repondre(res, 403, { erreur: 'Code invalide.' });
      }

      const cible = String(body.pseudo || '').trim().toLowerCase();
      if (!cible) return repondre(res, 400, { erreur: 'Pseudo manquant.' });
      const fiche = await Carnet.lire(cible);
      if (!fiche) return repondre(res, 404, { erreur: 'Compte introuvable.' });

      const banni = body.action !== 'debannir';
      await Carnet.definirBanni(cible, banni);

      // si ce compte a une session ouverte sur ce serveur la, effet immediat
      for (const c of comptes.values()) {
        if (c.pseudoBas === cible) {
          c.banni = banni;
          if (banni) {
            quitterTable(c); quitterTableRoulette(c); retirerDeLaFilePeriph(c.jetonRef);
            c.periph = null; c.periphMulti = null;
            if (c.pontMulti) abandonnerPontMulti(c);
          }
        }
      }

      return repondre(res, 200, { ok: true, pseudo: fiche.pseudo, banni });
    }

    // --- supprimer completement un compte (meme code que bannir) ---
    if (route === '/api/supprimer-compte' && req.method === 'POST') {
      const maintenantSup = Date.now();
      if (!Array.isArray(compte.codeEchecs)) compte.codeEchecs = [];
      compte.codeEchecs = compte.codeEchecs.filter(t => maintenantSup - t < 60000);
      if (compte.codeEchecs.length >= 5) {
        return repondre(res, 429, { erreur: 'Trop d\'essais. Reessayez dans une minute.' });
      }
      const codeNormS = String(body.code || '').trim().toLowerCase()
        .replace(/\s+/g, '').replace(/[''']/g, '');
      if (codeNormS !== 'exclusionfdp') {
        compte.codeEchecs.push(maintenantSup);
        return repondre(res, 403, { erreur: 'Code invalide.' });
      }

      const cibleSup = String(body.pseudo || '').trim().toLowerCase();
      if (!cibleSup) return repondre(res, 400, { erreur: 'Pseudo manquant.' });
      const ficheSup = await Carnet.lire(cibleSup);
      if (!ficheSup) return repondre(res, 404, { erreur: 'Compte introuvable.' });

      // si ce compte a une session ouverte, on le vire d\'abord de partout
      for (const c of comptes.values()) {
        if (c.pseudoBas === cibleSup) {
          c.banni = true;
          quitterTable(c); quitterTableRoulette(c); retirerDeLaFilePeriph(c.jetonRef);
          c.periph = null; c.periphMulti = null;
          if (c.pontMulti) abandonnerPontMulti(c);
        }
      }
      await Carnet.supprimer(cibleSup);
      return repondre(res, 200, { ok: true, pseudo: ficheSup.pseudo });
    }

    // --- changer le solde d\'un compte (meme code que bannir) ---
    if (route === '/api/modifier-solde' && req.method === 'POST') {
      const maintenantSol = Date.now();
      if (!Array.isArray(compte.codeEchecs)) compte.codeEchecs = [];
      compte.codeEchecs = compte.codeEchecs.filter(t => maintenantSol - t < 60000);
      if (compte.codeEchecs.length >= 5) {
        return repondre(res, 429, { erreur: 'Trop d\'essais. Reessayez dans une minute.' });
      }
      const codeNormO = String(body.code || '').trim().toLowerCase()
        .replace(/\s+/g, '').replace(/[''']/g, '');
      if (codeNormO !== 'exclusionfdp') {
        compte.codeEchecs.push(maintenantSol);
        return repondre(res, 403, { erreur: 'Code invalide.' });
      }

      const cibleSol = String(body.pseudo || '').trim().toLowerCase();
      if (!cibleSol) return repondre(res, 400, { erreur: 'Pseudo manquant.' });
      const nouveauSolde = Number(body.solde);
      if (!Number.isFinite(nouveauSolde) || nouveauSolde < 0) {
        return repondre(res, 400, { erreur: 'Montant invalide.' });
      }
      const ficheSol = await Carnet.lire(cibleSol);
      if (!ficheSol) return repondre(res, 404, { erreur: 'Compte introuvable.' });

      await Carnet.definirSolde(cibleSol, nouveauSolde);
      for (const c of comptes.values()) {
        if (c.pseudoBas === cibleSol) c.solde = nouveauSolde;
      }
      return repondre(res, 200, { ok: true, pseudo: ficheSol.pseudo, solde: nouveauSolde });
    }

    // --- razzia : supprimer la base d'un joueur pour qu'il la repose ailleurs
    // (meme code que bannir) ---
    if (route === '/api/razzia-supprimer-base' && req.method === 'POST') {
      const maintenantRz = Date.now();
      if (!Array.isArray(compte.codeEchecs)) compte.codeEchecs = [];
      compte.codeEchecs = compte.codeEchecs.filter(t => maintenantRz - t < 60000);
      if (compte.codeEchecs.length >= 5) {
        return repondre(res, 429, { erreur: 'Trop d\'essais. Reessayez dans une minute.' });
      }
      const codeNormRz = String(body.code || '').trim().toLowerCase()
        .replace(/\s+/g, '').replace(/[''']/g, '');
      if (codeNormRz !== 'exclusionfdp') {
        compte.codeEchecs.push(maintenantRz);
        return repondre(res, 403, { erreur: 'Code invalide.' });
      }
      if (!rzCharge) return repondre(res, 503, { erreur: 'La carte se prépare, réessaie dans quelques secondes.' });
      await rzSynchroniser(true);

      const cibleRz = String(body.pseudo || '').trim().toLowerCase();
      if (!cibleRz) return repondre(res, 400, { erreur: 'Pseudo manquant.' });
      const j = RZJ[cibleRz];
      if (!j || !j.base) return repondre(res, 404, { erreur: 'Ce joueur n\'a pas de base posée.' });

      // annule tout groupe en route qui lui appartient ou qui vise sa base
      for (const id of Object.keys(RZG)) {
        const g = RZG[id];
        if (g.proprio === cibleRz || (g.cible && g.cible.type === 'base' && g.cible.pseudo === cibleRz)) {
          delete RZG[id];
        }
      }
      j.base = null;
      j.bouclier = true;
      j.bouclierRetireLe = 0;
      j.feuJusqua = 0;
      // action sensible : on s'assure que la suppression est vraiment ecrite
      // dans la base avant de dire "ok" (sinon un redemarrage du serveur
      // pourrait faire revenir l'ancienne base, comme avant ce correctif)
      rzADIRTY = true;
      let ecrite = await rzSauverMaintenant(true);
      for (let essai = 0; !ecrite && essai < 3; essai++) { await new Promise(r => setTimeout(r, 400)); ecrite = await rzSauverMaintenant(true); }
      if (!ecrite) return repondre(res, 503, { erreur: 'La base a bien ete enlevee ici, mais je n\'arrive pas a l\'enregistrer durablement (souci reseau). Reessaie dans une minute.' });
      return repondre(res, 200, { ok: true, pseudo: j.pseudo });
    }

    // --- ma fiche (ecran profil) ---
    /* ================= RAZZIA ================= */
    if (route.startsWith('/api/razzia-')) {
      if (!rzCharge) return repondre(res, 503, { erreur: 'La carte se prépare, réessaie dans quelques secondes.' });
      await rzSynchroniser(route === '/api/razzia-base' || route === '/api/razzia-deplacer-base');
      const moi = rzJoueur(compte);
      const pb = compte.pseudoBas;
      const now = Date.now();
      const FEU = 'Ta base brûle : tu ne peux rien faire avant la fin de l\'incendie ou la réparation.';

      if (route === '/api/razzia-monde') {
        return repondre(res, 200, rzVue(compte, url.searchParams.get('depuis') || body.depuis));
      }

      if (route === '/api/razzia-base' && req.method === 'POST') {
        if (moi.base) return repondre(res, 409, { erreur: 'Ta base est déjà posée.' });
        const p = rzPoint([body.lon, body.lat]);
        if (!p || !rzDansZone(p)) return repondre(res, 400, { erreur: 'Cet endroit est hors de la zone ouverte.' });
        if (Object.values(RZJ).some(j => j.base && rzDist([j.base.lon, j.base.lat], p) < 25))
          return repondre(res, 409, { erreur: 'Ce bâtiment est déjà la base de quelqu\'un.' });
        const forme = (Array.isArray(body.forme) ? body.forme : []).slice(0, 80).map(rzPoint).filter(Boolean);
        moi.base = { lon: p[0], lat: p[1], forme: forme.length >= 3 ? forme : null,
                     haut: Math.max(6, Math.min(120, Number(body.haut) || 18)) };
        moi.bouclier = true;
        // action sensible (une fois posee, on veut etre sur qu'elle survit a
        // un redemarrage du serveur) : on attend une vraie confirmation
        rzADIRTY = true;
        let poseeOk = await rzSauverMaintenant(true);
        for (let essai = 0; !poseeOk && essai < 3; essai++) { await new Promise(r => setTimeout(r, 400)); poseeOk = await rzSauverMaintenant(true); }
        if (!poseeOk) { moi.base = null; return repondre(res, 503, { erreur: 'Souci reseau, ta base n\'a pas pu etre enregistree. Reessaie.' }); }
        return repondre(res, 200, rzVue(compte, now));
      }

      if (!moi.base && route !== '/api/razzia-alliance') return repondre(res, 409, { erreur: 'Pose d\'abord ta base.' });

      /* changer sa base d'emplacement : une seule fois par compte */
      if (route === '/api/razzia-deplacer-base' && req.method === 'POST') {
        if (moi.deplaceUtilise) return repondre(res, 409, { erreur: 'Tu as déjà utilisé ton changement d\'emplacement.' });
        if (rzEnFeu(moi)) return repondre(res, 409, { erreur: FEU });
        if (Object.values(RZG).some(g => g.etat === 'route' && g.cible && g.cible.type === 'base' && g.cible.pseudo === pb))
          return repondre(res, 409, { erreur: 'Des koalas sont en train d\'attaquer ta base : attends qu\'ils arrivent.' });
        const p = rzPoint([body.lon, body.lat]);
        if (!p || !rzDansZone(p)) return repondre(res, 400, { erreur: 'Cet endroit est hors de la zone ouverte.' });
        if (rzDist([moi.base.lon, moi.base.lat], p) < 25) return repondre(res, 409, { erreur: 'C\'est déjà là que se trouve ta base.' });
        if (Object.keys(RZJ).some(k => k !== pb && RZJ[k].base && rzDist([RZJ[k].base.lon, RZJ[k].base.lat], p) < 25))
          return repondre(res, 409, { erreur: 'Ce bâtiment est déjà la base de quelqu\'un.' });
        const forme = (Array.isArray(body.forme) ? body.forme : []).slice(0, 80).map(rzPoint).filter(Boolean);
        const ancienne = moi.base;
        moi.base = { lon: p[0], lat: p[1], forme: forme.length >= 3 ? forme : null,
                     haut: Math.max(6, Math.min(120, Number(body.haut) || 18)) };
        moi.deplaceUtilise = true;
        rzADIRTY = true;
        let ok = await rzSauverMaintenant(true);
        for (let essai = 0; !ok && essai < 3; essai++) { await new Promise(r => setTimeout(r, 400)); ok = await rzSauverMaintenant(true); }
        if (!ok) { moi.base = ancienne; moi.deplaceUtilise = false; return repondre(res, 503, { erreur: 'Souci réseau, ta base n\'a pas pu être déplacée. Réessaie.' }); }
        rzEvenement(pb, 'Ta base a changé d\'emplacement.', 'info');
        return repondre(res, 200, rzVue(compte, now));
      }

      if (route === '/api/razzia-acheter' && req.method === 'POST') {
        if (rzEnFeu(moi)) return repondre(res, 409, { erreur: FEU });
        const quoi = String(body.quoi || '');
        const n = Math.max(1, Math.min(500, Math.floor(Number(body.n) || 1)));
        if (quoi === 'koala' || quoi === 'humain') {
          const prix = RZ_PRIX.koala * n;
          if (compte.solde < prix) return repondre(res, 409, { erreur: 'Pas assez d\'argent.' });
          compte.solde = sous(compte.solde - prix); moi.stock.nu += n;
        } else if (RZ_NIV_ARME[quoi]) {
          if (moi.armurerie < RZ_NIV_ARME[quoi]) return repondre(res, 409, { erreur: 'Améliore ton armurerie pour débloquer ce pistolet.' });
          if (moi.stock.nu < n) return repondre(res, 409, { erreur: 'Il faut un koala sans arme par pistolet acheté. Achète d\'abord des koalas.' });
          const prix = RZ_PRIX[quoi] * n;
          if (compte.solde < prix) return repondre(res, 409, { erreur: 'Pas assez d\'argent.' });
          compte.solde = sous(compte.solde - prix); moi.stock.nu -= n; moi.stock[quoi] += n;
        } else if (quoi === 'limousine') {
          if (moi.limousine) return repondre(res, 409, { erreur: 'Tu as déjà ta limousine.' });
          if (compte.solde < RZ_PRIX_LIMOUSINE) return repondre(res, 409, { erreur: 'Pas assez d\'argent.' });
          compte.solde = sous(compte.solde - RZ_PRIX_LIMOUSINE); moi.limousine = true;
        } else return repondre(res, 400, { erreur: 'Achat inconnu.' });
        const info = siegeDe(compte); if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
        Carnet.enregistrer(compte); rzSauver();
        return repondre(res, 200, rzVue(compte, now));
      }

      if (route === '/api/razzia-ameliorer' && req.method === 'POST') {
        if (rzEnFeu(moi)) return repondre(res, 409, { erreur: FEU });
        const quoi = String(body.quoi || '');
        let prix;
        if (quoi === 'defense') { if (moi.defense >= 5) return repondre(res, 409, { erreur: 'Défense au maximum.' }); prix = RZ_PRIX_DEFENSE[moi.defense]; }
        else if (quoi === 'armurerie') { if (moi.armurerie >= RZ_ARMURERIE_MAX) return repondre(res, 409, { erreur: 'Armurerie au maximum.' }); prix = RZ_PRIX_ARMURERIE[moi.armurerie]; }
        else return repondre(res, 400, { erreur: 'Amélioration inconnue.' });
        if (compte.solde < prix) return repondre(res, 409, { erreur: 'Pas assez d\'argent.' });
        compte.solde = sous(compte.solde - prix);
        if (quoi === 'defense') moi.defense++; else moi.armurerie++;
        const info = siegeDe(compte); if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
        Carnet.enregistrer(compte); rzSauver();
        return repondre(res, 200, rzVue(compte, now));
      }

      if (route === '/api/razzia-repartition' && req.method === 'POST') {
        const v = RZ_COTES.map(c => Math.max(0, Number(body[c]) || 0));
        const s = v.reduce((a, b) => a + b, 0);
        if (s <= 0) return repondre(res, 400, { erreur: 'Répartition vide.' });
        const r = v.map(x => Math.round(x / s * 100)); r[0] += 100 - r.reduce((a, b) => a + b, 0);
        RZ_COTES.forEach((c, i) => { moi.repartition[c] = r[i]; });
        rzSauver();
        return repondre(res, 200, rzVue(compte, now));
      }

      if (route === '/api/razzia-bouclier' && req.method === 'POST') {
        if (rzEnFeu(moi)) return repondre(res, 409, { erreur: FEU });
        if (body.actif) {
          if (moi.bouclier) return repondre(res, 200, rzVue(compte, now));
          const reste = moi.bouclierRetireLe + RZ_BOUCLIER_ATTENTE - now;
          if (reste > 0) return repondre(res, 409, { erreur: 'Bouclier disponible dans ' + Math.ceil(reste / 60000) + ' min.' });
          moi.bouclier = true;
        } else if (moi.bouclier) { moi.bouclier = false; moi.bouclierRetireLe = now; }
        rzSauver();
        return repondre(res, 200, rzVue(compte, now));
      }

      if (route === '/api/razzia-reparer' && req.method === 'POST') {
        if (!rzEnFeu(moi)) return repondre(res, 409, { erreur: 'Ta base ne brûle pas.' });
        if (compte.solde < RZ_REPARATION) return repondre(res, 409, { erreur: 'Il faut 5 000 € pour réparer.' });
        compte.solde = sous(compte.solde - RZ_REPARATION);
        moi.feuJusqua = 0;
        const info = siegeDe(compte); if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
        Carnet.enregistrer(compte); rzSauver();
        return repondre(res, 200, rzVue(compte, now));
      }

      if (route === '/api/razzia-mur-construire' && req.method === 'POST') {
        if (rzEnFeu(moi)) return repondre(res, 409, { erreur: FEU });
        if (!moi.base) return repondre(res, 409, { erreur: 'Pose d\'abord ta base.' });
        const a = rzPoint(body.a), b = rzPoint(body.b);
        if (!a || !b || !rzDansZone(a) || !rzDansZone(b)) return repondre(res, 400, { erreur: 'Muraille hors de la zone ouverte.' });
        const longueur = rzDist(a, b);
        if (longueur < RZ_MUR_LONGUEUR_MIN || longueur > RZ_MUR_LONGUEUR_MAX) return repondre(res, 400, { erreur: 'Une muraille doit faire entre ' + RZ_MUR_LONGUEUR_MIN + ' et ' + RZ_MUR_LONGUEUR_MAX + ' m.' });
        const mesMurs = Object.values(RZ_MURS).filter(m => m.proprio === pb);
        const prochE = p => rzDist(p, [moi.base.lon, moi.base.lat]) <= RZ_MUR_CHAINE_MAX
          || mesMurs.some(m => rzDist(p, m.a) <= RZ_MUR_CHAINE_MAX || rzDist(p, m.b) <= RZ_MUR_CHAINE_MAX);
        if (!prochE(a) && !prochE(b)) return repondre(res, 409, { erreur: 'Cette muraille doit se relier à ta base ou à une muraille déjà posée.' });
        const portail = !!body.portail;
        const cout = portail ? RZ_PORTAIL_COUT : RZ_MUR_COUT;
        if (compte.solde < cout) return repondre(res, 409, { erreur: 'Il faut ' + cout.toLocaleString('fr-FR') + ' € pour poser ' + (portail ? 'un portail' : 'une muraille') + '.' });
        compte.solde = sous(compte.solde - cout);
        const m = { id: 'm' + (rzMurCompteur++), proprio: pb, a, b, garnison: rzVide(), portail, ouvert: false, basculeLe: 0 };
        RZ_MURS[m.id] = m;
        const info = siegeDe(compte); if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
        Carnet.enregistrer(compte); rzSauver();
        return repondre(res, 200, rzVue(compte, now));
      }

      if (route === '/api/razzia-portail-basculer' && req.method === 'POST') {
        const m = RZ_MURS[String(body.id || '')];
        if (!m) return repondre(res, 404, { erreur: 'Portail introuvable.' });
        if (m.proprio !== pb) return repondre(res, 409, { erreur: 'Ce n\'est pas ton portail.' });
        if (!m.portail) return repondre(res, 409, { erreur: 'Ce n\'est pas un portail.' });
        m.ouvert = !m.ouvert; m.basculeLe = now;
        rzSauver();
        return repondre(res, 200, rzVue(compte, now));
      }

      if (route === '/api/razzia-mur-demolir' && req.method === 'POST') {
        const m = RZ_MURS[String(body.id || '')];
        if (!m) return repondre(res, 404, { erreur: 'Muraille introuvable.' });
        if (m.proprio !== pb) return repondre(res, 409, { erreur: 'Ce n\'est pas ta muraille.' });
        const remboursement = Math.round((m.portail ? RZ_PORTAIL_COUT : RZ_MUR_COUT) * (RZ_MUR_REMBOURS / RZ_MUR_COUT));
        RZ_TYPES.forEach(t => { moi.stock[t] += m.garnison[t] | 0; });   // la garnison rentre a la base, saine et sauve
        delete RZ_MURS[m.id];
        compte.solde = sous(compte.solde + remboursement);
        const info = siegeDe(compte); if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
        Carnet.enregistrer(compte); rzSauver();
        return repondre(res, 200, Object.assign(rzVue(compte, now), { remboursement }));
      }

      if (route === '/api/razzia-envoyer' && req.method === 'POST') {
        if (rzEnFeu(moi)) return repondre(res, 409, { erreur: FEU });
        const cible = body.cible || {};
        let depart, g = null, unites;
        if (body.groupe) {
          g = RZG[String(body.groupe)];
          if (!g || g.proprio !== pb) return repondre(res, 404, { erreur: 'Groupe introuvable.' });
          if (g.etat === 'poste') depart = g.pos;
          else if (g.etat === 'route') depart = rzPositionActuelle(g, now);
          if (!depart) return repondre(res, 409, { erreur: 'Ce groupe ne peut pas être redirigé maintenant.' });
        } else {
          unites = rzPropre(body.unites);
          if (!rzTotal(unites)) return repondre(res, 400, { erreur: 'Choisis au moins un koala.' });
          if (RZ_TYPES.some(t => unites[t] > moi.stock[t])) return repondre(res, 409, { erreur: 'Tu n\'as pas tous ces koalas à la base.' });
          if (rzGroupesDe(pb).length >= RZ_MAX_GROUPES) return repondre(res, 409, { erreur: RZ_MAX_GROUPES + ' groupes dehors au maximum.' });
          depart = [moi.base.lon, moi.base.lat];
        }
        let arrivee, c;
        if (cible.type === 'base') {
          const v = RZJ[String(cible.pseudo || '')];
          if (!v || !v.base || cible.pseudo === pb) return repondre(res, 404, { erreur: 'Base introuvable.' });
          if (rzAllies(pb, cible.pseudo)) return repondre(res, 409, { erreur: 'Tu ne peux pas attaquer un allié.' });
          if (v.bouclier) return repondre(res, 409, { erreur: 'Cette base est sous bouclier.' });
          arrivee = [v.base.lon, v.base.lat];
          c = { type: 'base', pseudo: String(cible.pseudo), cote: RZ_COTES.indexOf(cible.cote) >= 0 ? cible.cote : 'devant' };
        } else if (cible.type === 'poste' || cible.type === 'batb') {
          const poste = RZ_POSTES.find(p => p.id === (cible.type === 'batb' ? 'batb' : String(cible.id || '')));
          if (!poste) return repondre(res, 404, { erreur: 'Poste introuvable.' });
          arrivee = [poste.lon, poste.lat]; c = { type: 'poste', id: poste.id };
        } else if (cible.type === 'bandit') {
          const b = RZ_BANDITS.find(x => x.id === String(cible.id || ''));
          if (!b) return repondre(res, 404, { erreur: 'Bandits introuvables.' });
          rzBanditRafraichir(b, now);
          if (!rzBanditVivant(b, now)) return repondre(res, 409, { erreur: 'Ce camp a été vaincu récemment. Il revient bientôt.' });
          arrivee = [b.lon, b.lat]; c = { type: 'bandit', id: b.id };
        } else if (cible.type === 'groupe') {
          const cg = RZG[String(cible.id || '')];
          if (!cg || cg.proprio === pb) return repondre(res, 404, { erreur: 'Groupe introuvable.' });
          if (rzAllies(pb, cg.proprio)) return repondre(res, 409, { erreur: 'Tu ne peux pas attaquer un allié.' });
          const p = rzPositionActuelle(cg, now);
          if (!p) return repondre(res, 404, { erreur: 'Groupe introuvable.' });
          arrivee = p; c = { type: 'groupe', id: cg.id };
        } else if (cible.type === 'mur') {
          const m = RZ_MURS[String(cible.id || '')];
          if (!m) return repondre(res, 404, { erreur: 'Muraille introuvable.' });
          arrivee = [(m.a[0] + m.b[0]) / 2, (m.a[1] + m.b[1]) / 2];
          c = m.proprio === pb ? { type: 'mur-renfort', id: m.id } : { type: 'mur', id: m.id };
        } else if (cible.type === 'maison') {
          arrivee = [moi.base.lon, moi.base.lat]; c = { type: 'maison' };
        } else {
          const p = rzPoint([cible.lon, cible.lat]);
          if (!p || !rzDansZone(p)) return repondre(res, 400, { erreur: 'Destination hors de la zone ouverte.' });
          arrivee = p; c = { type: 'point' };
        }
        if (!moi.limousine && Array.isArray(body.etapes) && body.etapes.some(e => e && e.limo)) return repondre(res, 409, { erreur: 'Tu n\'as pas de limousine.' });
        const plan = rzPlanifier(depart, arrivee, body.etapes, now);
        if (!plan) return repondre(res, 400, { erreur: 'Trajet refusé. Réessaie.' });
        // une muraille ennemie encore debout bloque le passage : il faut d'abord la detruire
        for (const e of plan.etapes) {
          if (e.type !== 'pied') continue;
          const mBloque = rzMurSurChemin(pb, e.coords, c.type === 'mur' || c.type === 'mur-renfort' ? c.id : null);
          if (mBloque) return repondre(res, 409, { erreur: 'Une muraille de ' + (RZJ[mBloque.proprio] ? RZJ[mBloque.proprio].pseudo : '?') + ' bloque ce chemin : il faut d\'abord la détruire.' });
        }
        if (c.type === 'base' && moi.bouclier) { moi.bouclier = false; moi.bouclierRetireLe = now; }   // attaquer fait tomber son propre bouclier
        if (!g) {
          RZ_TYPES.forEach(t => { moi.stock[t] -= unites[t]; });
          g = { id: 'g' + (rzCompteur++), proprio: pb, unites };
          RZG[g.id] = g;
        }
        g.etat = 'route'; g.pos = null; g.cible = c; g.etapes = plan.etapes; g.fin = plan.fin; g.cagnotte = 0; g.gagne = 0;
        rzSauver();
        return repondre(res, 200, Object.assign(rzVue(compte, now), { groupe: g.id }));
      }

      if (route === '/api/razzia-alliance' && req.method === 'POST') {
        const autre = String(body.pseudo || '');
        const lui = RZJ[autre];
        if (!lui || autre === pb) return repondre(res, 404, { erreur: 'Joueur introuvable.' });
        const action = String(body.action || '');
        const oter = (arr, x) => { const i = arr.indexOf(x); if (i >= 0) arr.splice(i, 1); };
        if (action === 'demander') {
          if (moi.allies.indexOf(autre) >= 0) return repondre(res, 409, { erreur: 'Vous êtes déjà alliés.' });
          if (moi.demandes.indexOf(autre) >= 0) {           // il l'avait deja demande : on accepte
            oter(moi.demandes, autre); moi.allies.push(autre); if (lui.allies.indexOf(pb) < 0) lui.allies.push(pb);
            rzEvenement(autre, moi.pseudo + ' a accepté ton alliance.', 'bon');
          } else if (lui.demandes.indexOf(pb) < 0) {
            lui.demandes.push(pb);
            rzEvenement(autre, moi.pseudo + ' te propose une alliance. Touche sa base pour répondre.', 'info');
          }
        } else if (action === 'accepter') {
          if (moi.demandes.indexOf(autre) < 0) return repondre(res, 409, { erreur: 'Aucune demande de sa part.' });
          oter(moi.demandes, autre);
          if (moi.allies.indexOf(autre) < 0) moi.allies.push(autre);
          if (lui.allies.indexOf(pb) < 0) lui.allies.push(pb);
          rzEvenement(autre, moi.pseudo + ' a accepté ton alliance.', 'bon');
        } else if (action === 'refuser') {
          oter(moi.demandes, autre);
        } else if (action === 'rompre') {
          oter(moi.allies, autre); oter(lui.allies, pb);
          rzEvenement(autre, moi.pseudo + ' a rompu votre alliance.', 'mauvais');
        } else return repondre(res, 400, { erreur: 'Action inconnue.' });
        rzSauver();
        return repondre(res, 200, rzVue(compte, now));
      }

      return repondre(res, 404, { erreur: 'route inconnue' });
    }

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

/* Ouvre une session pour un joueur reconnu. Un joueur ne peut etre
   connecte qu\'une fois : ouvrir une session ferme la precedente, sinon
   deux appareils feraient diverger le meme solde. */
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
    banni:     !!fiche.banni,
    penalty: null,                       // aucune serie de penaltys en cours
    periph:  null,                       // aucune course de periph en cours
    periphMulti: null,                   // pas dans un groupe de course multijoueur
    bois: null,                          // pas dans la poursuite du bois de Boulogne
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

  if (table.jeu === 'poker') {
    const k = table.places.findIndex(p => p && p.jeton === compte.jetonRef);
    if (k >= 0) pkQuitter(table, k);
    return;
  }

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

/* pour la simulation des cotes de Tower Rush (node -e "require('./serveur.js')") :
   rien n\'est exporte d\'autre, et le site demarre exactement comme avant */
module.exports = { towerTirer, towerAmpFor, towerPeriodFor, towerRollFactor, TOWER_NIVEAUX, TOWER_MULT_MAX };

Carnet.demarrer().then(() => {
  if (require.main !== module) return;
  serveur.listen(PORT, () => {
    console.log('Casino Messina - le salon est ouvert sur le port ' + PORT);
  });
});
