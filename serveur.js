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

/* ---------- Tower Rush : les cotes (refonte) ----------
   Avant : un lacher bien vise ne tombait jamais, et chaque etage
   multipliait en moyenne par plus de 1, sans plafond. Un bon joueur
   pouvait donc monter indefiniment (0,10 € -> 16 000 €, soit x160 000).

   Maintenant la tour a DOUZE niveaux et un plafond dur de x100.
   - Chaque niveau a une chance de tenir, meme avec un lacher parfait
     (TOWER_SURVIE). Un lacher imprecis ajoute son propre risque par-dessus.
   - Si l'etage tient, le multiplicateur cumule suit en moyenne
     TOWER_ECHELLE (x1,13 au 1er niveau ... x100 au 12e), avec un peu de
     hasard a chaque etage (la cote peut rester inferieure a x1).
   - Le hasard de chaque etage est INDEPENDANT des precedents : aucune
     strategie d'encaissement ne peut faire mieux que l'esperance du
     premier niveau (0,85 x 1,13 = 0,96). Plus on monte, plus l'esperance
     baisse (0,78 au 7e niveau, 0,11 au sommet).
   - Probabilite d'atteindre le sommet depuis le depart, lacher parfait
     a chaque fois : 0,85 x 0,82 x ... x 0,25 = 0,109 %.
   - Etage gele : aucun risque, mais la cote reste proche de x1 (moyenne
     0,99) et il ne compte pas comme un niveau.
   Simulation (voir le rapport) : retour moyen ~0,90 a 0,96 par euro mise
   selon la facon de jouer, jamais plus de x100.                        */
const TOWER_NIVEAUX  = 12;
const TOWER_MULT_MAX = 100;
const TOWER_SURVIE   = [0.85, 0.82, 0.78, 0.74, 0.70, 0.66, 0.60, 0.54, 0.48, 0.42, 0.36, 0.25];
const TOWER_ECHELLE  = [1.13, 1.36, 1.71, 2.26, 3.13, 4.5, 7.0, 10.5, 15.5, 22, 30, 100];

function towerRollFactor(niveau) {
  const k = Math.min(niveau, TOWER_NIVEAUX - 1);
  const ratio = k === 0 ? TOWER_ECHELLE[0] : TOWER_ECHELLE[k] / TOWER_ECHELLE[k - 1];
  const a = k === 0 ? 0.40 : 0.15;                    // hasard de moyenne 1
  return ratio * towerRand(1 - a, 1 + a);
}

/* Un lacher, calcule entierement ici. Modifie `tour` et renvoie l'issue :
   'rate' (l'etage tombe a cote), 'glisse' (la tour s'effondre) ou 'pose'.
   Exporte en bas de fichier pour la simulation des cotes. */
function towerTirer(tour, angle) {
  const n = tour.floors.length;
  const niveau = tour.niveau | 0;
  const amp = towerAmpFor(n);
  const etaitGele = tour.frozenLeft > 0;
  if (etaitGele) angle *= 0.2;

  const errRatio = Math.abs(angle) / amp;
  const safeT = 0.44, missT = Math.max(0.6, 0.92 - n * 0.016);
  const edgeT = towerClamp((errRatio - safeT) / Math.max(0.001, missT - safeT), 0, 1);
  const missChance = etaitGele ? 0 : edgeT * edgeT;
  if (Math.random() < missChance) return { issue: 'rate', angle: angle };

  // le risque propre au niveau, meme avec un lacher parfait
  const tombe = !etaitGele && Math.random() >= TOWER_SURVIE[Math.min(niveau, TOWER_NIVEAUX - 1)];
  if (tombe && errRatio > 0.25) return { issue: 'rate', angle: angle };

  const facteur = etaitGele ? towerRand(0.92, 1.06) : towerRollFactor(niveau);
  if (etaitGele) tour.frozenLeft--;
  else tour.niveau = niveau + 1;
  const parfait = !etaitGele && errRatio < 0.1 && facteur >= 1;

  // pas d'arrondi ici : seul le gain final (mise x totalMult) est arrondi
  tour.totalMult = Math.min(TOWER_MULT_MAX, tour.totalMult * facteur);
  const nouveauLean = tour.leanSum + angle * 0.58;
  const glisse = tombe || ((tour.frozenLeft <= 0) && Math.abs(nouveauLean) > 58);
  tour.leanSum = nouveauLean;
  tour.visOffset = towerClamp(tour.visOffset + towerClamp(angle * 0.34, -22, 22), -74, 74);
  tour.floors.push({ mult: facteur, lean: tour.visOffset });
  if (glisse) return { issue: 'glisse', angle: angle, facteur: facteur };

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

/* ===================================================================
   POKER — Texas Hold'em sans limite, uniquement entre vrais joueurs
   -------------------------------------------------------------------
   Meme principe que le blackjack : le serveur tient les cartes, les
   tours et le chronometre ; le battement fait avancer la donne.
   - Pas de bots, jamais. Moins de deux joueurs : la table attend.
   - Les jetons d'un joueur, c'est son vrai solde : chaque mise est
     debitee tout de suite, le pot est verse au(x) gagnant(s) a la fin.
   - Aucune commission (pas de rake) : tout le pot revient aux joueurs.
   - Les cartes privees d'un joueur ne quittent JAMAIS le serveur vers
     un autre joueur, sauf a l'abattage si ce joueur ne s'est pas couche.
   Tous les montants de la donne sont comptes en CENTIMES (entiers)
   pour qu'aucun centime ne se perde en route.
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
const pkDe = r => r === 14 ? "d'As" : 'de ' + PK_NP[r];
function pkNomMain(h) {
  const k = h.k;
  switch (h.cat) {
    case 8: return k[1] === 14 ? 'Quinte flush royale' : 'Quinte flush hauteur ' + PK_NS[k[1]];
    case 7: return 'Carré ' + pkDe(k[1]);
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

/* verse de l'argent a un joueur de la donne, meme s'il a quitte la table
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
    dire(table, 'En attente d’un deuxième joueur.');
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
  dire(table, 'Donne n°' + table.donne + ' : les cartes sont distribuées.');
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

/* ---------- une action d'un joueur (ou du chronometre) ---------- */
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
    j.couche = true; pkLabel(j, 'Couché', 'fold');
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

/* ---------- entre deux tours d'encheres ---------- */
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
    dire(table, 'Abattage : les cartes sont retournées.');
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
    // tout le monde est parti : chacun recupere ce qu'il avait mis
    J.forEach((j, i) => { if (j) pkCrediter(table, i, j.total); });
    res.titre = 'Donne annulée';
    res.sous = 'Tout le monde a quitté la table : les mises sont rendues.';
  } else if (cont.length === 1) {
    const w = cont[0];
    pkCrediter(table, w, potTotal);
    res.gagnants = [w];
    res.titre = nomDe(w) + ' remporte ' + eurC(potTotal);
    res.sous = 'Tous les autres joueurs se sont couchés.';
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
      res.lignes.push([nomPot + ' · ' + eurC(pt.amount), ws.map(nomDe).join(' & ') + (ws.length > 1 ? ' (partagé)' : '')]);
    });
    const gagnantsPrincipal = principal.length ? principal : (pots[0] ? pots[0].elig : cont);
    res.gagnants = gagnantsPrincipal.slice();
    const wh = ev[gagnantsPrincipal[0]];
    res.cartesGagnantes = wh.cards.slice();
    res.titre = gagnantsPrincipal.length > 1 ? 'Pot partagé' : nomDe(gagnantsPrincipal[0]) + ' gagne ' + eurC(J[gagnantsPrincipal[0]].gain);
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
    if (m && enCours) pkConclure(table);   // rend l'argent qui serait encore au milieu
    table.main = null; table.resultat = null;
    table.phase = 'attente';
    table.message = '';
    table.chat = []; table.chatId = 0;
  }
  touche(table);
}

/* ---------- le battement du poker ---------- */
function battementPoker(table, now) {
  // les absents perdent leur place (et se couchent s'ils etaient en jeu)
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
        dire(table, 'En attente d’un deuxième joueur.');
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
    // la donne en cours ne concerne cette place que si c'est bien le meme joueur
    const j = j0 && (!p || p.jeton === j0.jeton) ? j0 : null;
    // un joueur parti en pleine donne : sa place reste "fantome" jusqu'a la fin
    if (!p && !(j && j.jeton)) return null;
    const estMoi = i === moiIndex;
    let cartes = [];
    if (j) {
      if (estMoi || j.montre) cartes = j.cartes.slice();        // les miennes, ou abattage
      else if (!j.couche) cartes = j.cartes.map(() => null);   // dos de cartes, rien d'autre
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
  // une fois la donne conclue, le pot a ete verse : il n'y a plus rien au milieu
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
  neuveTablePoker('poker', 'Médina d’Or')
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
function chatPour(table, jeton) {
  return table.chat.map(m => ({
    id: m.id, nom: m.nom, texte: m.texte, systeme: !!m.systeme, t: m.t || 0,
    moi: !!(m.jeton && m.jeton === jeton),
    cadeau: m.cadeau ? {
      de: m.cadeau.de, a: m.cadeau.a, montant: m.cadeau.montant,
      pourMoi: m.cadeau.aJeton === jeton,     // c'est moi qui reçois
      deMoi:   m.cadeau.deJeton === jeton     // c'est moi qui offre
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

/* ce que la page d'un joueur voit des AUTRES joueurs reels de sa course.
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
      compte.periphMultiErreur = 'Solde insuffisant : la course a démarré sans vous.';
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

      if (table.jeu === 'poker') {
        // une place vraiment libre (pas celle d'un joueur parti en pleine donne)
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
      /* on ne peut appuyer sur "Multijoueur" que depuis l'accueil du jeu : une
         course encore ouverte ici a donc ete abandonnee (page rechargee, onglet
         ferme en pleine course). Elle est perdue, exactement comme en solo
         (/api/periph-demarrer), au lieu de bloquer le multijoueur pour toujours. */
      if (compte.periphMulti) {
        majGroupeCoursePeriph(compte, { statut: 'crash' });
        compte.periphMulti = null;
      }
      if (compte.periph) { compte.periph = null; Carnet.enregistrer(compte); }
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
          /* depuis combien de temps la course est partie ici : chaque page cale
             son "3, 2, 1, GO" sur ce meme instant, au lieu de partir quand son
             propre sondage (toutes les 700 ms, plus le reseau) s'en apercoit */
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
           c'est ce que les autres pages dessinent. Avant, seule la fraction du
           troncon etait envoyee, et elle etait recombinee ici avec le palier du
           serveur, qui retarde sur celui de la page : la voiture sautait.
           Ca ne sert qu'a l'affichage, jamais a un gain ; on borne quand meme
           a ce qui est physiquement possible depuis le depart. */
        if (body.d !== undefined) {
          const course = compte.periph;
          const vmax = course && course.voiture === VOITURE_PREMIUM_INDICE ? VITESSE_MAX_PERIPH_PREMIUM : VITESSE_MAX_PERIPH;
          const possible = course ? (Date.now() - course.depart) / 1000 * vmax + 30 : Infinity;
          m.d = Math.max(0, Math.min(distancePeriph(ECHELLE_PERIPH.length), possible, Number(body.d) || 0));
          m.v = Math.max(0, Math.min(300, Number(body.v) || 0));
          /* l'instant de la mesure : a son arrivee ici, moins le trajet aller
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

      if (r.issue === 'glisse') {
        const perdu = tour.mise;
        compte.tower = null;
        Carnet.enregistrer(compte);
        return repondre(res, 200, {
          ok: true, rate: false, glisse: true, facteur: r.facteur, lean: tour.visOffset,
          totalMult: tour.totalMult, perdu: perdu, solde: compte.solde
        });
      }

      // le sommet (12e niveau, ou le plafond x100) : on encaisse d'office
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
      if (tour.floors.length < 1) return repondre(res, 400, { erreur: 'Posez au moins un étage avant d’encaisser.' });

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
   rien n'est exporte d'autre, et le site demarre exactement comme avant */
module.exports = { towerTirer, towerAmpFor, towerPeriodFor, TOWER_NIVEAUX, TOWER_MULT_MAX, TOWER_SURVIE, TOWER_ECHELLE };

Carnet.demarrer().then(() => {
  if (require.main !== module) return;
  serveur.listen(PORT, () => {
    console.log('Casino Messina — le salon est ouvert sur le port ' + PORT);
  });
});
