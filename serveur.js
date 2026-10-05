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
const PECHE_MAX_JOUR  = 20000;   // maximum de poissons peches par jour et par joueur

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
/* la GT Hybride : 500 km/h, 45 000 € */
const PRIX_VOITURE_HYBRIDE     = 45000;
const VOITURE_HYBRIDE_INDICE   = 5;
const VITESSE_MAX_PERIPH_HYBRIDE = 500 / 3.6;
function choisirVoiture(compte, v) {
  v = Number(v) | 0;
  if (v === VOITURE_HYBRIDE_INDICE && compte.voitureHybride) return VOITURE_HYBRIDE_INDICE;
  if (v === VOITURE_PREMIUM_INDICE && compte.voiturePremium) return VOITURE_PREMIUM_INDICE;
  return bornerVoitureNormale(v);
}
function vmaxPeriph(voiture) {
  return voiture === VOITURE_HYBRIDE_INDICE ? VITESSE_MAX_PERIPH_HYBRIDE
       : voiture === VOITURE_PREMIUM_INDICE ? VITESSE_MAX_PERIPH_PREMIUM : VITESSE_MAX_PERIPH;
}

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

const TOWER_NIVEAUX  = 30;
const TOWER_MULT_MAX = 30;      // gain maximum : 30 fois la mise (100 EUR -> 3 000 EUR)
const TOWER_GAIN_MAX = 30000;

/* ---------- Tower Rush : les cotes (v6, plus proche du vrai jeu) ----------
   Le resultat ne depend PAS de la visee : a chaque etage, le hasard decide.
     12 % : la tour s'effondre (mise perdue)
     88 % : l'etage tient et donne un multiplicateur au hasard :
        10 % x0,4 | 12 % x0,6 | 18 % x0,8 | 14 % x1 | 17 % x1,15 | 13 % x1,3
         9 % x1,8 |  5 % x2,5 |  2 % x3
   Chaque etage rend ~97,5 % en moyenne (0,88 x 1,1075).
   Plafond : x30 de la mise, encaisse d'office.                          */
const TOWER_P_CHUTE = 0.12;
const TOWER_TABLE = [[0.4, .10], [0.6, .12], [0.8, .18], [1, .14], [1.15, .17], [1.3, .13], [1.8, .09], [2.5, .05], [3, .02]];
function towerAlea() { return crypto.randomInt(0, 1000000000) / 1000000000; }
function towerRollFactor() {
  let r = towerAlea(), a = 0;
  for (const [m, p] of TOWER_TABLE) { a += p; if (r < a) return m; }
  return TOWER_TABLE[0][0];
}

/* Un lacher, calcule entierement ici. Modifie `tour` et renvoie l'issue :
   'rate' (effondrement, tire au hasard) ou 'pose'. */
function towerTirer(tour, angle) {
  const n = tour.floors.length;
  const niveau = tour.niveau | 0;
  const amp = towerAmpFor(n);
  const etaitGele = tour.frozenLeft > 0;

  if (!etaitGele && towerAlea() < TOWER_P_CHUTE) {
    // pour l'animation : l'etage part franchement sur le cote
    const sens = angle ? Math.sign(angle) : (Math.random() < 0.5 ? -1 : 1);
    return { issue: 'rate', angle: sens * amp * 0.95 };
  }

  const facteur = etaitGele ? Math.round(towerRand(0.95, 1.05) * 100) / 100 : towerRollFactor();
  if (etaitGele) tour.frozenLeft--;
  else tour.niveau = niveau + 1;
  const parfait = !etaitGele && facteur >= 2;

  tour.totalMult = Math.min(TOWER_MULT_MAX, tour.totalMult * facteur);
  tour.leanSum = 0;
  tour.visOffset = 0;
  tour.floors.push({ mult: facteur, lean: 0 });
  // l'etage pose s'affiche bien centre, quelle que soit la visee
  angle = angle * 0.15;

  // etage gele (sans risque) de temps en temps
  if (!etaitGele && Math.random() < 0.05) tour.frozenLeft = 1;

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
/* cote du Poulet apres k poulets trouves avec nbOs os caches (25 cases) */
/* cotes du Plinko (risque -> rangees -> case), identiques a la page */
const PLINKO_TABLES = {
  faible: { 8:[5.6,2.1,1.1,1,.5,1,1.1,2.1,5.6], 9:[5.6,2,1.6,1,.7,.7,1,1.6,2,5.6], 10:[8.9,3,1.4,1.1,1,.5,1,1.1,1.4,3,8.9],
    11:[8.4,3,1.9,1.3,1,.7,.7,1,1.3,1.9,3,8.4], 12:[10,3,1.6,1.4,1.1,1,.5,1,1.1,1.4,1.6,3,10], 13:[8.1,4,3,1.9,1.2,.9,.7,.7,.9,1.2,1.9,3,4,8.1],
    14:[7.1,4,1.9,1.4,1.3,1.1,1,.5,1,1.1,1.3,1.4,1.9,4,7.1], 15:[15,8,3,2,1.5,1.1,1,.7,.7,1,1.1,1.5,2,3,8,15],
    16:[16,9,2,1.4,1.4,1.2,1.1,1,.5,1,1.1,1.2,1.4,1.4,2,9,16] },
  moyen: { 8:[13,3,1.3,.7,.4,.7,1.3,3,13], 9:[18,4,1.7,.9,.5,.5,.9,1.7,4,18], 10:[22,5,2,1.4,.6,.4,.6,1.4,2,5,22],
    11:[24,6,3,1.8,.7,.5,.5,.7,1.8,3,6,24], 12:[33,11,4,2,1.1,.6,.3,.6,1.1,2,4,11,33], 13:[43,13,6,3,1.3,.7,.4,.4,.7,1.3,3,6,13,43],
    14:[58,15,7,4,1.9,1,.5,.2,.5,1,1.9,4,7,15,58], 15:[88,18,11,5,3,1.3,.5,.3,.3,.5,1.3,3,5,11,18,88],
    16:[110,41,10,5,3,1.5,1,.5,.3,.5,1,1.5,3,5,10,41,110] },
  eleve: { 8:[29,4,1.5,.3,.2,.3,1.5,4,29], 9:[43,7,2,.6,.2,.2,.6,2,7,43], 10:[76,10,3,.9,.3,.2,.3,.9,3,10,76],
    11:[120,14,5.2,1.4,.4,.2,.2,.4,1.4,5.2,14,120], 12:[170,24,8.1,2,.7,.2,.2,.2,.7,2,8.1,24,170], 13:[260,37,11,4,1,.2,.2,.2,.2,1,4,11,37,260],
    14:[420,56,18,5,1.9,.3,.2,.2,.2,.3,1.9,5,18,56,420], 15:[620,83,27,8,3,.5,.2,.2,.2,.2,.5,3,8,27,83,620],
    16:[1000,130,26,9,4,2,.2,.2,.2,.2,.2,2,4,9,26,130,1000] }
};
function crocoMult(nb, k) { let m = 0.99; for (let i = 0; i < k; i++) m *= (20 - i) / (20 - i - nb); return m; }
function molesMult(nb, k) { return 0.98 * Math.pow(7 / nb, k); }
function pouletMult(nbOs, k) {
  let m = 0.99;
  for (let i = 0; i < k; i++) m *= (25 - i) / (25 - i - nbOs);
  return m;   // brut : le gain est arrondi au centime, l'affichage tronque a 2 decimales
}

/* Koala Road (chicken road) : a chaque voie franchie, une chance fixe de
   se faire ecraser. Faible 1/25, Moyen 3/25, Eleve 5/25, Casse-cou 10/25
   (plus le risque est grand, plus la cote monte vite). 20 voies.
   Cote de la voie k = 0,99 / (1-p)^k. */
const KROAD_RISQUES  = { faible: 1 / 25, moyen: 3 / 25, eleve: 5 / 25, cassecou: 10 / 25 };
const KROAD_VOIES_MAX = 20;
function kroadMult(risque, k) { const p = KROAD_RISQUES[risque]; return 0.99 * Math.pow(1 / (1 - p), k); }

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
      voitureHybride: !!compte.voitureHybride,
      perso:     compte.perso || ancienne.perso || null,
      codesUtilises: Array.isArray(compte.codesUtilises) ? compte.codesUtilises : (ancienne.codesUtilises || []),
      points:    compte.points | 0,
      kroadVoies: compte.kroadVoies | 0,
      tx:        Array.isArray(compte.tx) ? compte.tx.slice(0, 60) : (ancienne.tx || []),
      pecheJour: compte.pecheJour || null,
      pecheAuj:  compte.pecheAuj | 0,
      blockJour: compte.blockJour || null,
      blockAuj:  compte.blockAuj | 0,
      blockBest: compte.blockBest | 0,
      blockVides: compte.blockVides | 0,
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
  table.places.forEach((p, i) => { if (p && p.type === 'humain') majSoldeCompte(p); if (p && p.type === 'humain' && cts(p.solde) >= 1) out.push(i); });
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
    if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
    Carnet.enregistrer(compte);
  }
}

/* pose un montant devant le joueur : il quitte VRAIMENT son solde */
function pkPoser(table, i, montantC) {
  const j = table.main.joueurs[i], p = table.places[i];
  if (!j || !p) return 0;
  majSoldeCompte(p);
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
    majSoldeCompte(p);
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
    if (p && p.type === 'humain') majSoldeCompte(p);
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

/* Le siege (blackjack, poker) garde une copie du solde. AVANT, cette copie
   ECRASAIT le vrai solde a chaque fin de main : tout ce qui avait ete perdu
   ailleurs entre-temps (roulette, tower, pont...) revenait tout seul, et on
   pouvait jouer gratuitement. Maintenant on ne pousse que ce qui a vraiment
   change A LA TABLE (la difference), puis on relit le vrai solde. */
function majSoldeCompte(p) {
  if (!p || p.type !== 'humain' || !p.jeton) return;
  const c = comptes.get(p.jeton);
  if (!c) return;
  if (typeof p.soldeRef !== 'number') p.soldeRef = p.solde;
  const d = sous(p.solde - p.soldeRef);
  if (d) c.solde = sous(Math.max(0, c.solde + d));
  p.solde = c.solde;
  p.soldeRef = c.solde;
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
  if (total > 0) { c.solde = sous(c.solde + total); soldeAuSiege(c); }
  p.mises = {};
}

function nouvelleMancheRoulette() {
  tableRoulette.phase = 'mise';
  tableRoulette.echeance = Date.now() + DUREE_MISE_ROULETTE;
  tableRoulette.numeroGagnant = null;
  tableRoulette.places.forEach(p => { if (p) { p.mises = {}; p.misesTour = {}; p.dernierGain = 0; p.derniereMiseTotale = 0; } });
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
      if (gains > 0) { c.solde = sous(c.solde + gains); soldeAuSiege(c); }
      if (miseTotale > 0) c.roulettes = (c.roulettes | 0) + 1;
      Carnet.enregistrer(c);
    }
    p.dernierGain = gains;
    p.derniereMiseTotale = miseTotale;
    if (miseTotale > 0) p.dernieresMises = Object.assign({}, p.mises);
    p.misesTour = Object.assign({}, p.mises);         // restent affichees pendant que la roue tourne
    p.mises = {};
  });

  tableRoulette.historique.unshift({ n: numero, c: couleur });
  tableRoulette.historique = tableRoulette.historique.slice(0, 14);

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
    places: t.places.map((p, i) => { if (!p) return null; const ms = t.phase === 'mise' ? p.mises : (p.misesTour || {});
      return { nom: p.nom, moi: i === moiIndex, couleur: p.couleur | 0, mises: ms,
      total: sous(Object.values(ms).reduce((a, b) => a + b, 0)), dernierGain: p.dernierGain || 0 }; }),
    dernieresMises: moi ? (moi.dernieresMises || {}) : {},
    mesMises: moi ? (t.phase === 'mise' ? moi.mises : (moi.misesTour || {})) : {},
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
  const voiture = choisirVoiture(compte, voitureDemandee);

  compte.solde  = sous(compte.solde - mise);
  compte.periph = { mise: mise, palier: 0, depart: Date.now(), voiture: voiture };
  compte.periphs = (compte.periphs | 0) + 1;

  const info = siegeDe(compte);
  if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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
const BOIS_VITESSE_MAX   = 550 / 3.6; // metres par seconde, turbo compris (marge au-dessus des 300 km/h de la voiture premium)

function planToledo(graine){
  let s=graine>>>0;
  const r=()=>{ s=(s+0x6D2B79F5)|0; let t=Math.imul(s^(s>>>15),1|s);
    t=(t+Math.imul(t^(t>>>7),61|t))^t; return ((t^(t>>>14))>>>0)/4294967296; };
  const PAS=50, VOIE=3.5, DIST=3000;
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


/* ===================================================================
   ROULETTE LIVE - une seule roue pour tout le site, tours en continu.
   Le numero est tire ICI au debut du lancement. Les mises sont prises
   pendant la phase 'mise' et payees a la fin du lancement.
   =================================================================== */
const RL_MISE = 12000, RL_TIRAGE = 9200, RL_RESULTAT = 4000;
const RL_ROUGES = [1,3,5,7,9,12,14,16,18,19,21,23,25,27,30,32,34,36];
const rlive = { tour: 1, phase: 'mise', debut: Date.now(), echeance: Date.now() + RL_MISE, numero: null, historique: [], gagnants: [], nbGagnants: 0, totalGagne: 0 };
function rlCouleur(n) { return n === 0 ? 'vert' : (RL_ROUGES.indexOf(n) >= 0 ? 'rouge' : 'noir'); }
/* valide une case de mise et renvoie { nums, mult } (mult = gain total pour 1 mise, mise comprise) */
function rlCase(cle) {
  const simples = { rouge: RL_ROUGES, noir: [], pair: [], impair: [], manque: [], passe: [] };
  for (let n = 1; n <= 36; n++) {
    if (RL_ROUGES.indexOf(n) < 0) simples.noir.push(n);
    (n % 2 ? simples.impair : simples.pair).push(n);
    (n <= 18 ? simples.manque : simples.passe).push(n);
  }
  if (simples[cle]) return { nums: simples[cle], mult: 2 };
  let m = /^d([123])$/.exec(cle); if (m) { const d = +m[1]; const nums = []; for (let n = d * 12 - 11; n <= d * 12; n++) nums.push(n); return { nums, mult: 3 }; }
  m = /^k([123])$/.exec(cle); if (m) { const c = +m[1]; const nums = []; for (let n = c; n <= 36; n += 3) nums.push(n); return { nums, mult: 3 }; }
  m = /^n:([0-9-]+)$/.exec(cle); if (!m) return null;
  const nums = m[1].split('-').map(Number).sort((a, b) => a - b);
  if (nums.some(n => !(Number.isInteger(n) && n >= 0 && n <= 36)) || new Set(nums).size !== nums.length) return null;
  const k = nums.length, key = nums.join('-');
  const row = n => Math.ceil(n / 3), col = n => (n - 1) % 3;
  if (k === 1) return { nums, mult: 36 };
  if (k === 2) {
    const [a, b] = nums;
    if (a === 0 && b >= 1 && b <= 3) return { nums, mult: 18 };
    if (a > 0 && ((b - a === 1 && row(a) === row(b)) || b - a === 3)) return { nums, mult: 18 };
    return null;
  }
  if (k === 3) {
    if (key === '0-1-2' || key === '0-2-3') return { nums, mult: 12 };
    if (nums[0] > 0 && col(nums[0]) === 0 && nums[1] === nums[0] + 1 && nums[2] === nums[0] + 2) return { nums, mult: 12 };
    return null;
  }
  if (k === 4) {
    if (key === '0-1-2-3') return { nums, mult: 9 };
    const a = nums[0];
    if (a > 0 && col(a) < 2 && key === [a, a + 1, a + 3, a + 4].join('-')) return { nums, mult: 9 };
    return null;
  }
  if (k === 6) {
    const a = nums[0];
    if (a > 0 && col(a) === 0 && a <= 31 && key === [a, a + 1, a + 2, a + 3, a + 4, a + 5].join('-')) return { nums, mult: 6 };
    return null;
  }
  return null;
}
function rlLancer() {
  rlive.numero = [0,32,15,19,4,21,2,25,17,34,6,27,13,36,11,30,8,23,10,5,24,16,33,1,20,14,31,9,22,18,29,7,28,12,35,3,26][crypto.randomInt(37)];
  rlive.phase = 'tirage'; rlive.debut = Date.now(); rlive.echeance = rlive.debut + RL_TIRAGE;
}
function rlPayer() {
  const n = rlive.numero, liste = []; let total = 0;
  for (const c of comptes.values()) {
    const r = c.rlive;
    if (!r || r.tour !== rlive.tour) continue;
    let gain = 0, mise = 0;
    Object.keys(r.mises).forEach(k => { const z = rlCase(k); if (!z) return; mise += r.mises[k]; if (z.nums.indexOf(n) >= 0) gain += r.mises[k] * z.mult; });
    gain = sous(gain);
    r.gain = gain; r.miseTotale = sous(mise); r.derniere = Object.assign({}, r.mises); r.paye = true;
    if (gain > 0) { c.solde = sous(c.solde + gain); soldeAuSiege(c); liste.push({ p: c.pseudo, g: gain }); total += gain; }
    Carnet.enregistrer(c);
  }
  liste.sort((a, b) => b.g - a.g);
  rlive.gagnants = liste.slice(0, 8); rlive.nbGagnants = liste.length; rlive.totalGagne = sous(total);
  rlive.historique.unshift(n); rlive.historique = rlive.historique.slice(0, 14);
  rlive.phase = 'resultat'; rlive.debut = Date.now(); rlive.echeance = rlive.debut + RL_RESULTAT;
}
function battementRlive() {
  const now = Date.now();
  if (now < rlive.echeance) return;
  if (rlive.phase === 'mise') rlLancer();
  else if (rlive.phase === 'tirage') rlPayer();
  else { rlive.tour++; rlive.phase = 'mise'; rlive.debut = now; rlive.echeance = now + RL_MISE; rlive.numero = null; }
}
setInterval(battementRlive, 100);
for (let i = 0; i < 10; i++) rlive.historique.push([0,32,15,19,4,21,2,25,17,34,6,27,13,36,11,30,8,23,10,5,24,16,33,1,20,14,31,9,22,18,29,7,28,12,35,3,26][crypto.randomInt(37)]);


/* ===================================================================
   RICH JOKER - slot 3x3, 5 lignes. Tout est tire ICI (RTP ~95 %).
   =================================================================== */
const RJ_PAY = { W: 120, L: 80, G: 40, O: 10, P: 10, C: 3 };   // x mise par ligne (3 identiques)
const RJ_LIGNES = [[0,0,0],[1,1,1],[2,2,2],[0,1,2],[2,1,0]];
const RJ_BV = [[5,30],[10,25],[15,16],[25,10],[35,6],[50,4],[75,3],['mini',1.6],['minor',.8],['major',.25],['grand',.03]];
const RJ_JP = { mini: 125, minor: 250, major: 750, grand: 5000 };
const RJ_BASE = { C: 30, P: 22, O: 20, G: 12, L: 7, W: 3 };
const RJ_REELS = [Object.assign({}, RJ_BASE, { B: 6 }), Object.assign({}, RJ_BASE, { K: 5 }), Object.assign({}, RJ_BASE, { B: 6 })];
const RJ_MISES = [0.1, 0.25, 0.5, 1, 2.5, 5, 10, 25, 50, 100];
function rjAlea() { return crypto.randomInt(0, 1000000000) / 1000000000; }
function rjPick(w) { let t = 0; for (const k in w) t += w[k]; let r = rjAlea() * t; for (const k in w) { r -= w[k]; if (r < 0) return k; } return Object.keys(w)[0]; }
function rjBonus() { let t = 0; for (const b of RJ_BV) t += b[1]; let r = rjAlea() * t; for (const b of RJ_BV) { r -= b[1]; if (r < 0) return b[0]; } return 5; }
function rjVal(v) { return typeof v === 'number' ? v : RJ_JP[v]; }
function rjTourner(mise) {
  const lb = mise / 5;
  const g = [[], [], []];
  for (let c = 0; c < 3; c++) for (let r = 0; r < 3; r++) { const s = rjPick(RJ_REELS[c]); g[c][r] = s === 'B' ? { s: 'B', v: rjBonus() } : { s }; }
  let gl = 0; const lignes = [];
  RJ_LIGNES.forEach((L, i) => {
    const t = [g[0][L[0]].s, g[1][L[1]].s, g[2][L[2]].s];
    if (t.some(x => x === 'B' || x === 'K')) return;
    const s = t.find(x => x !== 'W') || 'W';
    if (t.every(x => x === s || x === 'W') && RJ_PAY[s]) { gl += RJ_PAY[s] * lb; lignes.push({ i, g: sous(RJ_PAY[s] * lb) }); }
  });
  const nb = c => g[c].filter(x => x.s === 'B').length, aK = g[1].some(x => x.s === 'K');
  let collect = 0, respins = null, gf = 0;
  if (aK && (nb(0) || nb(2))) {
    if (nb(0) && nb(2)) {
      const L = g.map(col => col.map(x => (x.s === 'B' || x.s === 'K') ? x : null)); let left = 3; respins = [];
      while (left > 0) {
        left--; const nouveaux = [];
        for (let c = 0; c < 3; c++) for (let r = 0; r < 3; r++) if (!L[c][r] && rjAlea() < 0.10) { L[c][r] = c === 1 ? { s: 'K' } : { s: 'B', v: rjBonus() }; nouveaux.push([c, r]); left = 3; }
        respins.push({ grille: L.map(col => col.map(x => x ? Object.assign({}, x) : null)), nouveaux, reste: left });
      }
      let sum = 0, k = 0; L.forEach(col => col.forEach(x => { if (!x) return; if (x.s === 'B') sum += rjVal(x.v); else k++; }));
      gf = sum * k * lb;
    } else { let sum = 0; [0, 2].forEach(c => g[c].forEach(x => { if (x.s === 'B') sum += rjVal(x.v); })); collect = sum * lb; }
  }
  return { grille: g, lignes, gainLignes: sous(gl), collect: sous(collect), respins, gainFeature: sous(gf), gain: Math.min(10000, sous(gl + collect + gf)) };
}

function soldeAuSiege(compte) {
  const info = siegeDe(compte);
  if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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
/* ---------- historique, points et gros gains ----------
   Chaque requete note le solde avant ; a la reponse, la difference est
   rangee dans l'historique du joueur sous le nom du jeu. Ce qui a bouge
   ENTRE deux requetes (blackjack et roulette se reglent sur minuterie,
   ajustement admin) est range a part. Mises -> points de niveau (100 par
   euro mise). Gains de 5 EUR ou plus -> fil des gros gains de l'accueil. */

/* ===== SLOT GAMES : le moteur (le meme que dans la page) ===== */
const SLOTS_HOTE = {};
/* ===== MOTEUR DES MACHINES A SOUS (partage : page + serveur) =====
   Deux familles :
   - 'lignes'  : rouleaux, lignes de paiement de gauche a droite, joker (W)
                 qui remplace tout, symbole bonus (S) -> tours gratuits (gains x2),
                 ou pieces (C) -> chaque piece porte une valeur, 3+ pieces paient.
   - 'cascade' : grille 6x5, 8 symboles identiques ou plus n'importe ou gagnent,
                 ils disparaissent et d'autres tombent ; les multiplicateurs (M)
                 multiplient le gain du tour ; 4+ bonus (S) -> 15 tours gratuits
                 ou les multiplicateurs s'accumulent.
   Toutes les cotes sont en "fois la mise totale", multipliees par ech (reglage RTP). */
(function (racine) {
'use strict';
const L5x3 = [[1,1,1,1,1],[0,0,0,0,0],[2,2,2,2,2],[0,1,2,1,0],[2,1,0,1,2],[0,0,1,2,2],[2,2,1,0,0],[1,0,0,0,1],[1,2,2,2,1],[1,0,1,2,1]];
const L5x5 = [[0,0,0,0,0],[1,1,1,1,1],[2,2,2,2,2],[3,3,3,3,3],[4,4,4,4,4],[0,1,2,3,4],[4,3,2,1,0],[0,1,0,1,0],[1,0,1,0,1],[1,2,1,2,1],[2,1,2,1,2],[2,3,2,3,2],[3,2,3,2,3],[3,4,3,4,3],[4,3,4,3,4]];
const lettres = (h) => ({ A:{w:h,p:{3:.1,4:.5,5:1}}, K:{w:h,p:{3:.1,4:.5,5:1}}, Q:{w:h+2,p:{3:.1,4:.5,5:1}}, J:{w:h+2,p:{3:.1,4:.5,5:1}}, T:{w:h+2,p:{3:.1,4:.5,5:1}} });

const L5x4 = [[0,0,0,0,0],[1,1,1,1,1],[2,2,2,2,2],[3,3,3,3,3],[0,1,2,1,0],[1,2,3,2,1],[3,2,1,2,3],[2,1,0,1,2],[0,1,0,1,0],[1,0,1,0,1],
              [2,3,2,3,2],[3,2,3,2,3],[1,2,1,2,1],[2,1,2,1,2],[0,0,1,2,3],[3,3,2,1,0],[0,1,1,1,0],[3,2,2,2,3],[1,1,0,1,1],[2,2,3,2,2]];
const JEUX = {
  /* Mythology Zeus : 5 rouleaux x 4 rangees, 20 lignes. Wild expansif (remplit sa colonne),
     3 scatters ou plus = 10 tours gratuits ; pendant les tours gratuits chaque gain a un multiplicateur (x2 a x500). */
  zeus: { nom:'MYTHOLOGY ZEUS', type:'lignes', rows:4, cols:5, lignes:L5x4, ech:0.5258, fs:10, fsMult:1, etend:true, fsMultAlea:true,
          sym:{ ZE:{w:3,p:{3:2,4:8,5:25}}, EA:{w:4,p:{3:1,4:4,5:12}}, HE:{w:5,p:{3:.8,4:3,5:8}}, DI:{w:7,p:{3:.5,4:1.5,5:4}}, SP:{w:8,p:{3:.4,4:1.2,5:3}}, HT:{w:9,p:{3:.3,4:1,5:2.5}}, CL:{w:9,p:{3:.3,4:1,5:2.5}} },
          W:{w:1.1}, S:{w:0.95} }
};
const VAL_PIECES = [[1,40],[2,25],[3,15],[5,10],[10,6],[25,3],[50,1]];
const VAL_MULT   = [[2,30],[3,22],[5,16],[10,12],[15,7],[25,5],[50,3],[100,1.5],[250,.4],[500,.1]];
const GAIN_MAX = 5000;       // jamais plus de 5000 fois la mise

function tirerPoids(liste, r) { let t = 0; for (const [, w] of liste) t += w; let x = r() * t; for (const [v, w] of liste) { x -= w; if (x < 0) return v; } return liste[liste.length - 1][0]; }
function sac(jeu, avecSpeciaux) {
  const l = Object.keys(jeu.sym).map(k => [k, jeu.sym[k].w]);
  if (avecSpeciaux) { for (const k of ['W','S','C','M']) if (jeu[k]) l.push([k, jeu[k].w]); }
  return l;
}
function cellule(jeu, r, fs) {
  const k = tirerPoids(sac(jeu, true), r);
  if (k === 'C') return { k, v: tirerPoids(VAL_PIECES, r) };
  if (k === 'M') return { k, v: tirerPoids(VAL_MULT, r) };
  if (fs && k === 'S' && jeu.type === 'lignes') return { k: tirerPoids(sac(jeu, false), r) };   // pas de relance infinie en tours gratuits
  return { k };
}

/* --- un tour a lignes --- */
function tourLignes(jeu, r, fs) {
  const g = [];
  for (let c = 0; c < jeu.cols; c++) { g.push([]); for (let l = 0; l < jeu.rows; l++) g[c].push(cellule(jeu, r, fs)); }
  // Joker Lines : un joker qui tombe remplit toute sa colonne
  let avant = null; const etendues = [];
  if (jeu.etend) { avant = g.map(col => col.map(x => Object.assign({}, x)));
    g.forEach((col, c) => { if (col.some(x => x.k === 'W')) { etendues.push(c); for (let l = 0; l < jeu.rows; l++) col[l] = { k: 'W' }; } }); }
  const gains = []; let total = 0;
  const lire = (ln, i, ordre) => {
    let base = null, n = 0;
    for (const c of ordre) {
      const k = g[c][ln[c]].k;
      if (k === 'S' || k === 'C') break;
      if (k === 'W') { n++; continue; }
      if (base === null) { base = k; n++; continue; }
      if (k === base) n++; else break;
    }
    if (base === null && n >= 3) base = Object.keys(jeu.sym)[0];      // que des jokers : paie comme le meilleur symbole
    if (base && n >= 3 && jeu.sym[base].p[n]) {
      const m = jeu.sym[base].p[n] * jeu.ech * (fs ? jeu.fsMult || 1 : 1);
      total += m; gains.push({ ligne: i, n, m, cells: ordre.slice(0, n).map(c => [c, ln[c]]) });
      return n;
    }
    return 0;
  };
  const gd = [...Array(jeu.cols).keys()], dg = gd.slice().reverse();
  jeu.lignes.forEach((ln, i) => {
    const n = lire(ln, i, gd);
    if (jeu.deuxSens && n < jeu.cols) lire(ln, i, dg);   // Diamonds : les lignes paient aussi de droite a gauche
  });
  // Big Dollars : chaque tour gagnant tire un multiplicateur
  let multX = 1;
  if (jeu.fsMultAlea && fs && total > 0) { const x = r(); multX = x < .45 ? 2 : x < .75 ? 3 : x < .9 ? 5 : x < .97 ? 10 : x < .993 ? 25 : x < .999 ? 100 : 500; total *= multX; }
  if (jeu.multAleatoire && total > 0) { const x = r(); multX = x < .70 ? 1 : x < .88 ? 2 : x < .95 ? 3 : x < .99 ? 5 : 10; total *= multX; }
  let fsGagnes = 0, bonusPieces = 0; const cellsSpec = [];
  let nS = 0, nC = 0, sommeC = 0;
  g.forEach((col, c) => col.forEach((x, l) => { if (x.k === 'S') { nS++; cellsSpec.push([c,l]); } if (x.k === 'C') { nC++; sommeC += x.v; cellsSpec.push([c,l]); } }));
  if (jeu.fs && nS >= 3) fsGagnes = jeu.fs + (nS - 3) * 5;
  if (jeu.pieces && nC >= 3) { bonusPieces = sommeC * jeu.ech * .6; total += bonusPieces; }
  return { grille: g, avant, etendues, multX, gains, total, fsGagnes, bonusPieces, special: (fsGagnes || bonusPieces) ? cellsSpec : [] };
}

/* --- un tour en cascade --- */
function tourCascade(jeu, r, fs, multCumul) {
  const g = []; for (let c = 0; c < jeu.cols; c++) { g.push([]); for (let l = 0; l < jeu.rows; l++) g[c].push(cellule(jeu, r, fs)); }
  const etapes = []; let total = 0;
  for (let garde = 0; garde < 40; garde++) {
    const cpt = {};
    g.forEach(col => col.forEach(x => { if (jeu.sym[x.k]) cpt[x.k] = (cpt[x.k] || 0) + 1; }));
    const gagnants = Object.keys(cpt).filter(k => cpt[k] >= 8);
    if (!gagnants.length) break;
    let gainEtape = 0; const cells = [];
    gagnants.forEach(k => { const n = cpt[k], t = n >= 12 ? 2 : n >= 10 ? 1 : 0; gainEtape += jeu.sym[k].p[t] * jeu.ech;
      g.forEach((col, c) => col.forEach((x, l) => { if (x.k === k) cells.push([c, l]); })); });
    total += gainEtape;
    const avant = g.map(col => col.map(x => Object.assign({}, x)));
    // les gagnants disparaissent, le reste tombe, de nouveaux symboles arrivent par le haut
    for (let c = 0; c < jeu.cols; c++) {
      const reste = g[c].filter((x, l) => !cells.some(([cc, ll]) => cc === c && ll === l));
      const neufs = []; while (neufs.length + reste.length < jeu.rows) neufs.push(cellule(jeu, r, fs));
      g[c] = neufs.concat(reste);
    }
    etapes.push({ avant, cells, gain: gainEtape, apres: g.map(col => col.map(x => Object.assign({}, x))) });
  }
  let sommeM = 0; g.forEach(col => col.forEach(x => { if (x.k === 'M') sommeM += x.v; }));
  let mult = 1;
  if (total > 0 && sommeM > 0) { if (fs) { multCumul.v += sommeM; mult = multCumul.v; } else mult = sommeM; }
  else if (fs && multCumul.v > 0 && total > 0) mult = multCumul.v;
  let nS = 0; g.forEach(col => col.forEach(x => { if (x.k === 'S') nS++; }));
  // on compte aussi les bonus vus pendant les cascades
  etapes.forEach(e => e.avant.forEach(col => col.forEach(x => {})));
  let payeS = 0; if (nS >= 6) payeS = 100; else if (nS === 5) payeS = 5; else if (nS === 4) payeS = 3;
  payeS *= jeu.ech * .5;
  const fsGagnes = nS >= 4 ? (fs ? 5 : 15) : 0;
  return { grille: etapes.length ? etapes[0].avant : g, etapes, fin: g, gainBase: total, mult, total: total * mult + payeS, payeS, fsGagnes, sommeM };
}

/* --- une mise complete : le tour, puis les tours gratuits eventuels --- */
function jouer(id, r) {
  const jeu = JEUX[id];
  const multCumul = { v: 0 };
  const base = jeu.type === 'lignes' ? tourLignes(jeu, r, false) : tourCascade(jeu, r, false, multCumul);
  const gratuits = [];
  let reste = base.fsGagnes, total = base.total;
  while (reste > 0 && gratuits.length < 60) {
    reste--;
    const t = jeu.type === 'lignes' ? tourLignes(jeu, r, true) : tourCascade(jeu, r, true, multCumul);
    gratuits.push(t); total += t.total; reste += t.fsGagnes;
  }
  total = Math.min(GAIN_MAX, total);
  return { base, gratuits, total };
}
racine.SLOTS = { JEUX, jouer, GAIN_MAX };
})(SLOTS_HOTE);

const SLOTS = SLOTS_HOTE.SLOTS;
/* =====================================================================
   BLOCK : grille 8x8, 3 pieces a poser. Tout est verifie ici.
   Plateau entierement vide apres une explosion = +10 EUR (max 10 000 EUR / jour).
   ===================================================================== */
const BLOCK_GAIN = 10, BLOCK_MAX_JOUR = 10000;
const BK_FORMES = (() => {
  // pieces simples : petits et gros cubes, comme demande
  const L = [], aj = (p, w) => L.push({ c: p, w });
  const rect = (h, w) => { const p = []; for (let a = 0; a < h; a++) for (let b = 0; b < w; b++) p.push([a, b]); return p; };
  aj(rect(1,1), 3); aj(rect(2,2), 7); aj(rect(3,3), 9); aj(rect(2,3), 5); aj(rect(3,2), 5);
  aj(rect(1,2), 2); aj(rect(2,1), 2); aj(rect(1,3), 2); aj(rect(3,1), 2);
  return L;
})();
const BK_3x3 = BK_FORMES[2].c, BK_2x3 = BK_FORMES[3].c, BK_3x2 = BK_FORMES[4].c;
const BK_TOT = BK_FORMES.reduce((a, f) => a + f.w, 0);
function bkAlea() { return crypto.randomInt(0, 1000000) / 1000000; }
function bkForme() { let x = bkAlea() * BK_TOT; for (const f of BK_FORMES) { x -= f.w; if (x < 0) return f.c; } return BK_FORMES[0].c; }
function bkVide() { return Array.from({ length: 8 }, () => Array(8).fill(0)); }
function bkPeut(g, p, r, c) { for (const [a, b] of p) { const y = r + a, x = c + b; if (y < 0 || y > 7 || x < 0 || x > 7 || g[y][x]) return false; } return true; }
function bkPlaceQuelquePart(g, p) { for (let r = 0; r < 8; r++) for (let c = 0; c < 8; c++) if (bkPeut(g, p, r, c)) return [r, c]; return null; }
function bkPoserSur(g, p, r, c, col) {
  const h = g.map(l => l.slice()); for (const [a, b] of p) h[r + a][c + b] = col;
  const lignes = [], cols = [];
  for (let y = 0; y < 8; y++) if (h[y].every(v => v)) lignes.push(y);
  for (let x = 0; x < 8; x++) if (h.every(l => l[x])) cols.push(x);
  let n = 0; for (const y of lignes) for (let x = 0; x < 8; x++) { if (h[y][x]) { h[y][x] = 0; n++; } }
  for (const x of cols) for (let y = 0; y < 8; y++) { if (h[y][x]) { h[y][x] = 0; n++; } }
  return { g: h, lignes, cols, efface: n };
}
/* generateur "aidant" : on essaie beaucoup de lots et on garde souvent celui
   qui permet de faire des lignes, voire de vider tout le plateau */
/* version rapide en "masques de bits" : chaque rangee = un nombre de 0 a 255 */
const bkMasques = new Map();
function bkMasque(p) { let m = bkMasques.get(p); if (m) return m; const h = Math.max(...p.map(q => q[0])) + 1, w = Math.max(...p.map(q => q[1])) + 1; const rows = Array(h).fill(0); for (const [a, b] of p) rows[a] |= 1 << b; m = { rows, h, w, n: p.length }; bkMasques.set(p, m); return m; }
function bkBits(g) { return g.map(l => l.reduce((m, v, x) => v ? m | (1 << x) : m, 0)); }
function bkCompte(R) { let n = 0; for (const r of R) { let v = r; while (v) { v &= v - 1; n++; } } return n; }
function bkMeilleurePose(R, m) {
  let best = null;
  for (let r = 0; r + m.h <= 8; r++) for (let c = 0; c + m.w <= 8; c++) {
    let ok = true; for (let a = 0; a < m.h; a++) if (R[r + a] & (m.rows[a] << c)) { ok = false; break; }
    if (!ok) continue;
    const S = R.slice(); for (let a = 0; a < m.h; a++) S[r + a] |= m.rows[a] << c;
    let col = 255; for (const v of S) col &= v;
    let n = 0; for (let y = 0; y < 8; y++) if (S[y] === 255) { S[y] = 0; n++; }
    if (col) { for (let y = 0; y < 8; y++) S[y] &= ~col & 255; let v = col; while (v) { v &= v - 1; n++; } }
    const reste = bkCompte(S), sc = (reste === 0 ? 5000 : 0) + n * 120 - reste * 2;
    if (!best || sc > best.sc) best = { sc, S, n };
  }
  return best;
}
function bkJoueLot(g, lot) {
  const R0 = bkBits(g), M = lot.map(bkMasque); let best = null;
  const ordres = [[0,1,2],[0,2,1],[1,0,2],[1,2,0],[2,0,1],[2,1,0]];
  for (const o of ordres) {
    let R = R0, lignes = 0, ok = 0;
    for (const k of o) { const b = bkMeilleurePose(R, M[k]); if (!b) break; R = b.S; lignes += b.n; ok++; }
    const reste = bkCompte(R);
    const sc = ok * 10000 + (ok === 3 && reste === 0 ? 8000 : 0) + lignes * 150 - reste * 3;
    if (!best || sc > best.sc) best = { sc, ok, lignes, vide: ok === 3 && reste === 0 };
  }
  return best;
}
function bkLot(g) {
  // le lot type : 1 piece de 6 + 2 pieces de 9, si elles rentrent
  const type = [bkAlea() < .5 ? BK_2x3 : BK_3x2, BK_3x3, BK_3x3];
  const pl0 = g.reduce((a, l) => a + l.filter(v => v).length, 0);
  if ((pl0 < 6 || pl0 > 40) && bkAlea() < .6 && bkJoueLot(g, type).ok === 3) return type.map(p => ({ f: p, col: 1 + crypto.randomInt(0, 7) }));
  const plein = g.reduce((a, l) => a + l.filter(v => v).length, 0);
  const essais = plein <= 24 ? 90 : 50;
  let meilleur = null, jouable = null;
  for (let e = 0; e < essais; e++) {
    const lot = [bkForme(), bkForme(), bkForme()];
    const r = bkJoueLot(g, lot);
    if (r.ok === 3 && !jouable) jouable = lot;
    if (!meilleur || r.sc > meilleur.r.sc) meilleur = { lot, r };
  }
  // plateau presque vide : on cherche fort un lot qui le vide completement
  if (!meilleur.r.vide && plein >= 6 && plein <= 40) {
    for (let e = 0; e < 700; e++) { const lot = [bkForme(), bkForme(), bkForme()]; const r = bkJoueLot(g, lot); if (r.vide) { meilleur = { lot, r }; break; } }
  }
  // 80 % du temps : le lot le plus genereux ; sinon un lot jouable au hasard (un peu de difficulte)
  // plateau (presque) vide : pas d'aide, sinon on pourrait relancer des parties pour gagner sans jouer
  const lot = (plein >= 8 && (bkAlea() < .8 || !jouable)) ? meilleur.lot : (jouable || meilleur.lot);
  return lot.map(p => ({ f: p, col: 1 + crypto.randomInt(0, 7) }));
}
function bkNouvelle(compte) { const g = bkVide(); compte.block = { g, pieces: bkLot(g), score: 0, combo: 0, sansExplo: 0, coups: 0 }; return compte.block; }
function bkFini(b) { return !b.pieces.some(p => p && bkPlaceQuelquePart(b.g, p.f)); }
function bkVue(compte, extra) {
  const b = compte.block, jour = new Date().toISOString().slice(0, 10);
  if (compte.blockJour !== jour) { compte.blockJour = jour; compte.blockAuj = 0; }
  return Object.assign({ ok: true, g: b.g, pieces: b.pieces, score: b.score, combo: b.combo, best: compte.blockBest | 0, fini: bkFini(b), gainsJour: compte.blockAuj | 0, maxJour: BLOCK_MAX_JOUR, solde: compte.solde }, extra || {});
}

/* ===== 3 COIN VOLCANOES : moteur (partage page + serveur) =====
   5 rouleaux x 3 rangees, 20 lignes. Volcan = joker. Pieces de lave (C) : chacune porte
   une valeur ou un jackpot. 6 pieces ou plus = BONUS : les pieces restent collees,
   3 relances, chaque nouvelle piece remet le compteur a 3. Grille pleine = GRAND. */
function jouerVolcan(jeu, r) {
  const ROWS = 3, COLS = 5, L = jeu.lignes;
  const tire = (liste) => { let t = 0; for (const [, w] of liste) t += w; let x = r() * t; for (const [v, w] of liste) { x -= w; if (x < 0) return v; } return liste[liste.length - 1][0]; };
  const sacBase = Object.keys(jeu.sym).map(k => [k, jeu.sym[k].w]).concat([['W', jeu.W.w], ['C', jeu.C.w]]);
  const piece = () => tire(jeu.valeurs);
  const g = [];
  for (let c = 0; c < COLS; c++) { g.push([]); for (let l = 0; l < ROWS; l++) { const k = tire(sacBase); g[c].push(k === 'C' ? { k, v: piece() } : { k }); } }
  // lignes
  const gains = []; let lignes = 0;
  L.forEach((ln, i) => {
    let base = null, n = 0;
    for (let c = 0; c < COLS; c++) { const k = g[c][ln[c]].k; if (k === 'C') break; if (k === 'W') { n++; continue; } if (base === null) { base = k; n++; continue; } if (k === base) n++; else break; }
    if (base === null && n >= 3) base = Object.keys(jeu.sym)[0];
    if (base && n >= 3 && jeu.sym[base].p[n]) { const m = jeu.sym[base].p[n] * jeu.ech; lignes += m; gains.push({ ligne: i, n, m, cells: [...Array(n).keys()].map(c => [c, ln[c]]) }); }
  });
  const valeurDe = v => typeof v === 'number' ? v * jeu.echC : jeu.jackpots[v];
  // bonus
  let bonus = null;
  const depart = []; g.forEach((col, c) => col.forEach((x, l) => { if (x.k === 'C') depart.push([c, l, x.v]); }));
  if (depart.length >= jeu.declenche) {
    const pris = new Set(depart.map(([c, l]) => c * 3 + l)); const tours = []; let relances = 3;
    while (relances > 0 && pris.size < 15) {
      relances--; const nouv = [];
      for (let i = 0; i < 15; i++) if (!pris.has(i) && r() < jeu.qRelance) { nouv.push([Math.floor(i / 3), i % 3, piece()]); }
      nouv.forEach(([c, l]) => pris.add(c * 3 + l));
      if (nouv.length) relances = 3;
      tours.push({ nouv, relances });
    }
    const toutes = depart.concat(...tours.map(t => t.nouv));
    let somme = toutes.reduce((s, [, , v]) => s + valeurDe(v), 0);
    const plein = pris.size >= 15; if (plein) somme += jeu.jackpots.GRAND;
    bonus = { depart, tours, plein, total: somme };
  }
  let total = lignes + (bonus ? bonus.total : 0);
  return { base: { grille: g, gains, total: lignes }, bonus, total };
}

const VOLCAN = { lignes: [[1,1,1,1,1],[0,0,0,0,0],[2,2,2,2,2],[0,1,2,1,0],[2,1,0,1,2],[0,0,1,2,2],[2,2,1,0,0],[1,0,0,0,1],[1,2,2,2,1],[1,0,1,2,1],
  [1,2,1,0,1],[0,1,1,1,0],[2,1,1,1,2],[0,1,0,1,0],[2,1,2,1,2],[1,1,0,1,1],[1,1,2,1,1],[0,0,2,0,0],[2,2,0,2,2],[0,2,0,2,0]],
  ech: 1.20, echC: 1, declenche: 6, qRelance: .035,
  sym: { SEPT:{w:3,p:{3:2,4:6,5:20}}, CRO:{w:4,p:{3:1.2,4:4,5:12}}, BAR:{w:5,p:{3:.8,4:2.5,5:8}}, CLO:{w:6,p:{3:.6,4:1.6,5:5}}, COF:{w:6,p:{3:.6,4:1.6,5:5}},
         GB:{w:11,p:{3:.2,4:.8,5:2}}, GV:{w:11,p:{3:.2,4:.8,5:2}}, GP:{w:11,p:{3:.2,4:.8,5:2}} },
  W: { w: 4.5 }, C: { w: 9.8 },
  valeurs: [[1,30],[2,25],[3,16],[5,10],[8,6],[10,5],[15,3],['MINI',1.6],['MINOR',.45],['MAJOR',.04]],
  jackpots: { MINI:25, MINOR:100, MAJOR:1000, GRAND:5000 } };

const SLOTS_OUVERTS = ['zeus', 'volcan'];
const SLOTS_MISES = [0.2,0.4,0.6,1,2,5,10,20,50,100,200,500];

/* =====================================================================
   CRASH GAME (avion) : une seule partie partagee par tous les joueurs.
   Tout se decide ici : le point de crash, les mises, les encaissements.
   ===================================================================== */
const AV_K = 0.085, AV_PRE = 5000, AV_PAUSE = 3200, AV_MIN = 0.10, AV_MAX = 150, AV_XMAX = 10000;
const AVION = { phase: 'attente', debut: Date.now(), crash: 2, round: 1, paris: [], file: [], hist: [], top: [] };
function avTirage() { const u = crypto.randomInt(0, 1000000000) / 1000000000; return Math.min(AV_XMAX, Math.max(1, Math.floor(0.97 / (1 - u) * 100) / 100)); }
function avBrut(ms) { return Math.exp(AV_K * ms / 1000); }
function avMult(ms) { return Math.floor(avBrut(ms) * 100) / 100; }
for (let i = 0; i < 20; i++) AVION.hist.push(avTirage());
AVION.crash = avTirage();
function avCrediter(b, x, horsRequete) {
  const c = b.compte, w = sous(b.mise * x);
  b.x = x; b.gain = w; b.encaisse = true;
  c.solde = sous(c.solde + w);
  if (horsRequete && typeof c.soldeSuivi === 'number') c.soldeSuivi = sous(c.soldeSuivi + w);
  noterMouvement(c, 'Crash Game', 'jeu', w);
  soldeAuSiege(c); Carnet.enregistrer(c);
  AVION.top.push({ p: c.pseudo, m: b.mise, x, g: w });
  AVION.top.sort((a, z) => z.g - a.g); if (AVION.top.length > 20) AVION.top.length = 20;
  return w;
}
function avNouveau() {
  for (const b of AVION.paris) {
    const c = b.compte; if (!Array.isArray(c.avMes)) c.avMes = [];
    c.avMes.unshift({ m: b.mise, x: b.encaisse ? b.x : 0, g: b.encaisse ? b.gain : 0, c: AVION.crash });
    if (c.avMes.length > 30) c.avMes.length = 30;
  }
  AVION.phase = 'attente'; AVION.debut = Date.now(); AVION.crash = avTirage(); AVION.round++;
  AVION.paris = AVION.file; AVION.file = [];
}
function battementAvion() {
  const now = Date.now(), el = now - AVION.debut;
  if (AVION.phase === 'attente') {
    if (el >= AV_PRE) { AVION.phase = 'vol'; AVION.debut = now; for (const b of AVION.paris) b.actif = true; }
  } else if (AVION.phase === 'vol') {
    const m = avMult(el), fini = avBrut(el) >= AVION.crash;
    for (const b of AVION.paris) if (b.actif && !b.encaisse && b.auto && b.auto < AVION.crash && (b.auto <= m || fini)) avCrediter(b, b.auto, true);
    if (fini) { AVION.phase = 'crash'; AVION.debut = now; AVION.hist.unshift(AVION.crash); if (AVION.hist.length > 60) AVION.hist.length = 60; }
  } else if (el >= AV_PAUSE) avNouveau();
}
setInterval(battementAvion, 50);
function avTrouver(compte, slot) {
  return AVION.paris.find(b => b.compte === compte && b.slot === slot) || AVION.file.find(b => b.compte === compte && b.slot === slot) || null;
}
function avEtat(compte) {
  const mes = [0, 1].map(s => {
    const f = AVION.file.find(b => b.compte === compte && b.slot === s);
    if (f) return { st: 'queued', m: f.mise, auto: f.auto };
    const b = AVION.paris.find(b => b.compte === compte && b.slot === s);
    if (!b) return { st: 'idle' };
    if (b.encaisse) return { st: 'idle', m: b.mise, x: b.x, g: b.gain };
    if (AVION.phase === 'attente') return { st: 'placed', m: b.mise, auto: b.auto };
    if (AVION.phase === 'vol') return { st: 'active', m: b.mise, auto: b.auto };
    return { st: 'idle', perdu: true, m: b.mise };
  });
  return {
    ok: true, phase: AVION.phase, ecoule: Date.now() - AVION.debut, round: AVION.round,
    crash: AVION.phase === 'crash' ? AVION.crash : null,
    paris: AVION.paris.map(b => ({ p: b.compte.pseudo, s: b.slot, m: b.mise, x: b.encaisse ? b.x : 0, g: b.encaisse ? b.gain : 0, moi: b.compte === compte })),
    hist: AVION.hist.slice(0, 30), top: AVION.top, mes, mesParis: (compte.avMes || []).slice(0, 30), solde: compte.solde
  };
}

/* =====================================================================
   LIVE BLACKJACK (la croupiere en video) : un joueur contre la banque.
   Tout est decide ici : le sabot, chaque carte, les gains.
   Regles : 6 jeux, la banque tire jusqu'a 16 et reste sur tous les 17,
   blackjack paye 3 pour 2, assurance 2 pour 1 (seulement si la carte
   visible de la banque est un As), double sur 2 cartes, un seul split.
   ===================================================================== */
const LBJ_MIN = 1, LBJ_MAX = 5000;
function lbjVal(c) { return c.h === 'A' ? 11 : (['10', 'V', 'D', 'R'].includes(c.h) ? 10 : parseInt(c.h, 10)); }
function lbjTotal(cartes) {
  let t = 0, as = 0;
  for (const c of cartes) { t += lbjVal(c); if (c.h === 'A') as++; }
  while (t > 21 && as) { t -= 10; as--; }
  return { t, souple: as > 0 && t <= 21 };
}
function lbjEstBJ(cartes) { return cartes.length === 2 && lbjTotal(cartes).t === 21; }
function lbjTirer(compte) {
  if (!compte.lbjSabot || compte.lbjSabot.length < 80) compte.lbjSabot = neufSabot();
  const c = compte.lbjSabot.pop();
  return { h: c.h, s: c.s, r: c.r };
}
function lbjPeutSplit(compte, r) {
  if (r.mains.length !== 1) return false;
  const m = r.mains[0];
  return m.cartes.length === 2 && lbjVal(m.cartes[0]) === lbjVal(m.cartes[1]) && compte.solde >= m.mise;
}
function lbjEtat(compte) {
  const r = compte.lbj;
  if (!r) return { ok: true, phase: 'mise', solde: compte.solde };
  const cachee = r.phase === 'joueur' || r.phase === 'assurance';
  const m = r.mains[r.active];
  return {
    ok: true, phase: r.phase, solde: compte.solde, active: r.active,
    mains: r.mains.map(x => ({ cartes: x.cartes, mise: x.mise, total: lbjTotal(x.cartes).t, souple: lbjTotal(x.cartes).souple, fini: x.fini, double: !!x.double, res: x.res || null, gain: x.gain || 0 })),
    croupier: cachee ? [r.croupier[0], null] : r.croupier,
    totalCroupier: cachee ? lbjTotal([r.croupier[0]]).t : lbjTotal(r.croupier).t,
    assurance: r.assurance || 0, resultat: r.resultat || null, gainTotal: r.gainTotal || 0,
    peut: r.phase !== 'joueur' || !m ? {} : {
      tirer: true, rester: true,
      doubler: m.cartes.length === 2 && compte.solde >= m.mise,
      split: lbjPeutSplit(compte, r)
    }
  };
}
function lbjSuivante(compte) {
  const r = compte.lbj;
  while (r.active < r.mains.length && r.mains[r.active].fini) r.active++;
  if (r.active < r.mains.length) {
    const m = r.mains[r.active];
    if (m.cartes.length === 1) { m.cartes.push(lbjTirer(compte)); r.seq.push({ qui: 'j', main: r.active, c: m.cartes[1] });
      if (m.splitAs || lbjTotal(m.cartes).t >= 21) { m.fini = true; return lbjSuivante(compte); } }
    return;
  }
  lbjBanque(compte);
}
function lbjBanque(compte) {
  const r = compte.lbj;
  r.phase = 'fin';
  r.seq.push({ qui: 'retourne', c: r.croupier[1] });
  const vivantes = r.mains.some(m => lbjTotal(m.cartes).t <= 21);
  if (vivantes) while (lbjTotal(r.croupier).t < 17) { const c = lbjTirer(compte); r.croupier.push(c); r.seq.push({ qui: 'c', c }); }
  lbjRegler(compte);
}
function lbjRegler(compte) {
  const r = compte.lbj;
  r.phase = 'fin';
  const tb = lbjTotal(r.croupier).t, bjB = lbjEstBJ(r.croupier);
  let gainTotal = 0;
  for (const m of r.mains) {
    const t = lbjTotal(m.cartes).t, bj = lbjEstBJ(m.cartes) && r.mains.length === 1;
    let g = 0, res;
    if (t > 21) res = 'bust';
    else if (bj && !bjB) { res = 'blackjack'; g = sous(m.mise * 2.5); }
    else if (bjB && !bj) res = 'perdu';
    else if (bj && bjB) { res = 'egalite'; g = m.mise; }
    else if (tb > 21) { res = 'banquebust'; g = sous(m.mise * 2); }
    else if (t > tb) { res = 'gagne'; g = sous(m.mise * 2); }
    else if (t === tb) { res = 'egalite'; g = m.mise; }
    else res = 'perdu';
    m.res = res; m.gain = g; m.fini = true; gainTotal += g;
  }
  if (r.assurance && bjB) gainTotal += sous(r.assurance * 3);
  r.gainTotal = sous(gainTotal);
  compte.solde = sous(compte.solde + r.gainTotal);
  const ordre = ['blackjack', 'banquebust', 'gagne', 'egalite', 'bust', 'perdu'];
  r.resultat = r.mains.map(m => m.res).sort((a, b) => ordre.indexOf(a) - ordre.indexOf(b))[0];
  r.fini = true;
}
function lbjApresDistribution(compte) {
  const r = compte.lbj, m = r.mains[0];
  const bjB = lbjEstBJ(r.croupier);
  if (lbjEstBJ(m.cartes) || bjB) { r.seq.push({ qui: 'retourne', c: r.croupier[1] }); lbjRegler(compte); return; }
  r.phase = 'joueur';
}
function lbjReponse(compte, res) {
  const r = compte.lbj;
  const e = lbjEtat(compte);
  e.seq = r ? r.seq : [];
  if (r) r.seq = [];
  if (r && r.fini) compte.lbj = null;
  soldeAuSiege(compte); Carnet.enregistrer(compte);
  if (res && res.__suivi) res.__suivi.nomJeu = compte.__lbe ? 'Live Blackjack Ethan' : 'Live Blackjack';
  return e;
}

const NOMS_SLOTS = { zeus:'Mythology Zeus', volcan:'3 Coin Volcanoes' };
const GROS_GAINS = [];
let grosGainsId = 0;
/* routes du blackjack un-contre-la-banque (servent aux deux tables live) */
function lbjRoutes(route, compte, body, res, req) {
  if (route === '/api/lbj-etat') {
    const e = lbjEtat(compte); e.seq = []; return repondre(res, 200, e);
  }
  if (route === '/api/lbj-miser' && req.method === 'POST') {
    if (compte.lbj) return repondre(res, 409, Object.assign(lbjEtat(compte), { erreur: 'Une main est deja en cours.' }));
    const mise = sous(Number(body.mise) || 0);
    if (!(mise >= LBJ_MIN && mise <= LBJ_MAX)) return repondre(res, 400, { erreur: 'Mise entre 1 € et 5 000 €.' });
    if (mise > compte.solde + 1e-9) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
    compte.solde = sous(compte.solde - mise);
    const r = compte.lbj = { mains: [{ cartes: [], mise }], croupier: [], active: 0, seq: [], phase: 'distribution' };
    const p1 = lbjTirer(compte), d1 = lbjTirer(compte), p2 = lbjTirer(compte), d2 = lbjTirer(compte);
    r.mains[0].cartes.push(p1, p2); r.croupier.push(d1, d2);
    r.seq.push({ qui: 'j', main: 0, c: p1 }, { qui: 'c', c: d1 }, { qui: 'j', main: 0, c: p2 }, { qui: 'cachee' });
    if (d1.h === 'A' && compte.solde >= sous(mise / 2)) r.phase = 'assurance';
    else lbjApresDistribution(compte);
    return repondre(res, 200, lbjReponse(compte, res));
  }
  if (route === '/api/lbj-assurance' && req.method === 'POST') {
    const r = compte.lbj;
    if (!r || r.phase !== 'assurance') return repondre(res, 409, { erreur: 'Pas d\'assurance possible.' });
    if (body.oui) { const a = sous(r.mains[0].mise / 2); if (a <= compte.solde) { compte.solde = sous(compte.solde - a); r.assurance = a; } }
    lbjApresDistribution(compte);
    return repondre(res, 200, lbjReponse(compte, res));
  }
  if (route === '/api/lbj-action' && req.method === 'POST') {
    const r = compte.lbj;
    if (!r || r.phase !== 'joueur') return repondre(res, 409, { erreur: 'Ce n\'est pas votre tour.' });
    const m = r.mains[r.active], a = String(body.action || '');
    if (a === 'tirer') {
      const c = lbjTirer(compte); m.cartes.push(c); r.seq.push({ qui: 'j', main: r.active, c });
      if (lbjTotal(m.cartes).t >= 21) { m.fini = true; lbjSuivante(compte); }
    } else if (a === 'rester') {
      m.fini = true; lbjSuivante(compte);
    } else if (a === 'doubler') {
      if (m.cartes.length !== 2 || compte.solde < m.mise) return repondre(res, 400, { erreur: 'Impossible de doubler.' });
      compte.solde = sous(compte.solde - m.mise); m.mise = sous(m.mise * 2); m.double = true;
      const c = lbjTirer(compte); m.cartes.push(c); r.seq.push({ qui: 'j', main: r.active, c });
      m.fini = true; lbjSuivante(compte);
    } else if (a === 'split') {
      if (!lbjPeutSplit(compte, r)) return repondre(res, 400, { erreur: 'Impossible de spliter.' });
      compte.solde = sous(compte.solde - m.mise);
      const as = m.cartes[0].h === 'A';
      const m2 = { cartes: [m.cartes.pop()], mise: m.mise, splitAs: as }; m.splitAs = as;
      r.mains.push(m2); r.seq.push({ qui: 'split' });
      const c = lbjTirer(compte); m.cartes.push(c); r.seq.push({ qui: 'j', main: 0, c });
      if (as || lbjTotal(m.cartes).t >= 21) { m.fini = true; lbjSuivante(compte); }
    } else return repondre(res, 400, { erreur: 'Action inconnue.' });
    return repondre(res, 200, lbjReponse(compte, res));
  }

}

/* =====================================================================
   LIVE BLACKJACK — TABLE PARTAGEE A 7 PLACES (le croupier LiveAvatar)
   Une seule table pour tout le casino. Le serveur decide tout : le sabot,
   chaque carte, l'ordre de jeu, les gains. Les pages ne font que montrer.
   Regles : 6 jeux, la banque tire jusqu'a 16 et reste sur tous les 17,
   blackjack paye 3 pour 2, assurance 2 pour 1 si la banque montre un As,
   double sur 2 cartes, un seul split (As splittes : une carte chacun).
   ===================================================================== */
let CROUPIER_ERREUR = null, CROUPIER_ERREUR_TEL = null, CROUPIER_OK = null;
/* la requete exacte envoyee a POST /v1/sessions/token (schema documente : mode, avatar_id, is_sandbox, max_session_duration, voice_agent{id}) */
function croupierDemande() {
  const n = v => String(v || '').trim().replace(/^["']|["']$/g, '');
  const d = { mode: 'FULL', avatar_id: n(process.env.LIVEAVATAR_AVATAR_ID), is_sandbox: n(process.env.LIVEAVATAR_SANDBOX) === '1',
              max_session_duration: Math.min(120, Number(process.env.LIVEAVATAR_MAX_SECONDES) || 120), voice_agent: { id: n(process.env.LIVEAVATAR_VOICE_AGENT_ID) } };
  return d;
}
function croupierMasquer(o) {
  return JSON.parse(JSON.stringify(o || null, (k, v) => /token|key|secret/i.test(k) && typeof v === 'string' ? '***masque*** (' + v.length + ' car.)' : v));
}
const LBT_PLACES = 7, LBT_MIN = 1, LBT_MAX = 5000;
const LBT_MISE_MS = 15000, LBT_ASSUR_MS = 8000, LBT_TOUR_MS = 15000, LBT_FIN_MS = 6000, LBT_ABSENT_MS = 30000;
const LBT = { phase: 'mise', places: new Array(LBT_PLACES).fill(null), croupier: [], seq: [], n: 0, debutN: 0,
              echeance: 0, active: null, sabot: [], manche: 0, ordre: [6, 5, 4, 3, 2, 1, 0] };
function lbtCompteVivant(p) {
  for (const c of comptes.values()) if (c.pseudoBas === p.pseudoBas) { p.compte = c; return c; }
  return p.compte;
}
function lbtTirer() { if (LBT.sabot.length < 80) LBT.sabot = neufSabot(); const c = LBT.sabot.pop(); return { h: c.h, s: c.s, r: c.r }; }
function lbtPousser(e) { e.n = ++LBT.n; LBT.seq.push(e); if (LBT.seq.length > 400) LBT.seq.shift(); }
function lbtPlaceDe(compte) { return LBT.places.findIndex(p => p && p.pseudoBas === compte.pseudoBas); }
function lbtJoueurs() { return LBT.ordre.filter(i => LBT.places[i] && LBT.places[i].mains.length); }
function lbtCrediter(p, montant) {
  if (!montant) return;
  const c = lbtCompteVivant(p);
  c.solde = sous(c.solde + montant); soldeAuSiege(c); Carnet.enregistrer(c);
}
function lbtDistribuer() {
  const qui = LBT.ordre.filter(i => LBT.places[i] && LBT.places[i].mise > 0);
  if (!qui.length) { LBT.phase = 'mise'; LBT.echeance = 0; return; }
  LBT.manche++; LBT.debutN = LBT.n + 1; LBT.croupier = [];
  lbtPousser({ qui: 'manche', manche: LBT.manche });
  for (const i of qui) { const p = LBT.places[i]; p.mains = [{ cartes: [], mise: p.mise }]; p.assurance = 0; p.jouait = true; }
  for (const tour of [0, 1]) {
    for (const i of qui) { const c = lbtTirer(); LBT.places[i].mains[0].cartes.push(c); lbtPousser({ qui: 'j', place: i, main: 0, c }); }
    const d = lbtTirer(); LBT.croupier.push(d);
    lbtPousser(tour === 0 ? { qui: 'c', c: d } : { qui: 'cachee' });
  }
  if (LBT.croupier[0].h === 'A') { LBT.phase = 'assurance'; LBT.echeance = Date.now() + LBT_ASSUR_MS; return; }
  lbtApresDonne();
}
function lbtApresDonne() {
  for (const p of LBT.places) if (p) p.assuranceVue = false;
  if (estBlackjack(LBT.croupier)) { lbtBanque(true); return; }
  for (const i of lbtJoueurs()) { const m = LBT.places[i].mains[0]; if (estBlackjack(m.cartes)) m.fini = true; }
  LBT.phase = 'joueurs'; LBT.active = null; lbtSuivant();
}
/* passe a la prochaine main a jouer (de droite a gauche, comme un vrai croupier) */
function lbtSuivant() {
  for (const i of lbtJoueurs()) {
    const p = LBT.places[i];
    for (let k = 0; k < p.mains.length; k++) {
      const m = p.mains[k];
      if (m.fini) continue;
      if (m.cartes.length === 1) {   // main issue d'un split : sa deuxieme carte
        const c = lbtTirer(); m.cartes.push(c); lbtPousser({ qui: 'j', place: i, main: k, c });
        if (m.splitAs || compter(m.cartes) >= 21) { m.fini = true; continue; }
      }
      LBT.active = { place: i, main: k }; LBT.echeance = Date.now() + LBT_TOUR_MS;
      lbtPousser({ qui: 'tour', place: i, main: k });
      return;
    }
  }
  lbtBanque(false);
}
function lbtBanque(bjBanque) {
  LBT.active = null; LBT.phase = 'croupier';
  lbtPousser({ qui: 'retourne', c: LBT.croupier[1] });
  const vivantes = lbtJoueurs().some(i => LBT.places[i].mains.some(m => compter(m.cartes) <= 21 && !(estBlackjack(m.cartes) && LBT.places[i].mains.length === 1)));
  if (!bjBanque && vivantes) while (compter(LBT.croupier) < 17) { const c = lbtTirer(); LBT.croupier.push(c); lbtPousser({ qui: 'c', c }); }
  lbtRegler();
}
function lbtRegler() {
  const tb = compter(LBT.croupier), bjB = estBlackjack(LBT.croupier);
  for (const i of lbtJoueurs()) {
    const p = LBT.places[i]; let total = 0;
    for (const m of p.mains) {
      const t = compter(m.cartes), bj = estBlackjack(m.cartes) && p.mains.length === 1;
      let g = 0, res;
      if (t > 21) res = 'bust';
      else if (bj && !bjB) { res = 'blackjack'; g = sous(m.mise * 2.5); }
      else if (bjB && !bj) res = 'perdu';
      else if (bj && bjB) { res = 'egalite'; g = m.mise; }
      else if (tb > 21) { res = 'banquebust'; g = sous(m.mise * 2); }
      else if (t > tb) { res = 'gagne'; g = sous(m.mise * 2); }
      else if (t === tb) { res = 'egalite'; g = m.mise; }
      else res = 'perdu';
      m.res = res; m.gain = g; m.fini = true; total += g;
    }
    if (p.assurance && bjB) total += sous(p.assurance * 3);
    p.gain = sous(total);
    lbtCrediter(p, p.gain);
  }
  lbtPousser({ qui: 'resultats' });
  LBT.phase = 'fin'; LBT.echeance = Date.now() + LBT_FIN_MS;
}
function lbtNettoyer() {
  for (let i = 0; i < LBT_PLACES; i++) {
    const p = LBT.places[i]; if (!p) continue;
    p.mains = []; p.mise = 0; p.assurance = 0; p.gain = 0; p.jouait = false;
    if (p.part || Date.now() - p.vu > LBT_ABSENT_MS) LBT.places[i] = null;
  }
  LBT.croupier = []; LBT.active = null; LBT.phase = 'mise'; LBT.echeance = 0;
  lbtPousser({ qui: 'nouvelle' });
}
function battementLbt() {
  const t = Date.now();
  // absents pendant la mise : on libere la place et on rend la mise
  if (LBT.phase === 'mise') for (let i = 0; i < LBT_PLACES; i++) {
    const p = LBT.places[i];
    if (p && t - p.vu > LBT_ABSENT_MS) { if (p.mise) lbtCrediter(p, p.mise); LBT.places[i] = null; }
  }
  if (LBT.phase === 'mise' && LBT.echeance && t >= LBT.echeance) lbtDistribuer();
  else if (LBT.phase === 'assurance' && t >= LBT.echeance) lbtApresDonne();
  else if (LBT.phase === 'joueurs' && LBT.active) {
    const p = LBT.places[LBT.active.place];
    const absent = !p || p.part || t - p.vu > LBT_ABSENT_MS;
    if (t >= LBT.echeance || absent) { if (p) p.mains[LBT.active.main].fini = true; lbtSuivant(); }
  }
  else if (LBT.phase === 'fin' && t >= LBT.echeance) lbtNettoyer();
}
setInterval(battementLbt, 200);
function lbtPeut(compte) {
  const a = LBT.active; if (LBT.phase !== 'joueurs' || !a) return {};
  const p = LBT.places[a.place]; if (!p || p.pseudoBas !== compte.pseudoBas) return {};
  const m = p.mains[a.main], c = lbtCompteVivant(p);
  return { tirer: true, rester: true,
           doubler: m.cartes.length === 2 && c.solde >= m.mise,
           split: p.mains.length === 1 && m.cartes.length === 2 && valeurCarte(m.cartes[0]) === valeurCarte(m.cartes[1]) && c.solde >= m.mise };
}
function lbtEtat(compte, depuis) {
  const cachee = LBT.phase === 'joueurs' || LBT.phase === 'assurance';
  const moi = lbtPlaceDe(compte);
  depuis = Number(depuis) || 0;
  const resync = depuis < LBT.debutN - 1 || depuis > LBT.n;
  return {
    ok: true, phase: LBT.phase, reste: LBT.echeance ? Math.max(0, LBT.echeance - Date.now()) : 0, manche: LBT.manche,
    n: LBT.n, resync, seq: resync ? [] : LBT.seq.filter(e => e.n > depuis).map(e => e.qui === 'cachee' ? { n: e.n, qui: 'cachee' } : e),
    moi, solde: compte.solde, active: LBT.active, peut: lbtPeut(compte),
    croupier: cachee ? (LBT.croupier.length ? [LBT.croupier[0], null] : []) : LBT.croupier,
    places: LBT.places.map((p, i) => p ? { pseudo: p.pseudo, moi: i === moi, mise: p.mise, assurance: p.assurance || 0, gain: p.gain || 0,
      mains: p.mains.map(m => ({ cartes: m.cartes, mise: m.mise, total: compter(m.cartes), fini: !!m.fini, double: !!m.double, res: m.res || null, gain: m.gain || 0 })) } : null)
  };
}
function lbtRoutes(route, compte, body, res) {
  const moi = lbtPlaceDe(compte);
  if (moi >= 0) { const p = LBT.places[moi]; p.vu = Date.now(); p.compte = compte; p.part = false; }
  if (route === '/api/lbt-etat') return repondre(res, 200, lbtEtat(compte, body.depuis));
  if (route === '/api/lbt-asseoir') {
    const voulu = Number.isInteger(body.place) ? body.place : -1;
    const libre = i => i >= 0 && i < LBT_PLACES && !LBT.places[i];
    if (moi >= 0) {
      const p = LBT.places[moi];
      if (voulu >= 0 && libre(voulu) && !p.mains.length && !p.mise) { LBT.places[voulu] = p; LBT.places[moi] = null; }
      return repondre(res, 200, lbtEtat(compte, 0));
    }
    let i = libre(voulu) ? voulu : [3, 2, 4, 1, 5, 0, 6].find(libre);
    if (i === undefined) return repondre(res, 200, Object.assign(lbtEtat(compte, 0), { complet: true }));
    LBT.places[i] = { pseudo: compte.pseudo, pseudoBas: compte.pseudoBas, compte, vu: Date.now(), mise: 0, mains: [], assurance: 0, gain: 0 };
    lbtPousser({ qui: 'assis', place: i, pseudo: compte.pseudo });
    return repondre(res, 200, lbtEtat(compte, 0));
  }
  if (route === '/api/lbt-quitter') {
    if (moi >= 0) {
      const p = LBT.places[moi];
      if (p.mains.length) p.part = true;               // sa main en cours se termine toute seule
      else { if (p.mise) lbtCrediter(p, p.mise); LBT.places[moi] = null; lbtPousser({ qui: 'parti', place: moi }); }
    }
    return repondre(res, 200, { ok: true });
  }
  if (moi < 0) return repondre(res, 409, { erreur: 'Asseyez-vous d\'abord a la table.' });
  const p = LBT.places[moi];
  if (route === '/api/lbt-miser') {
    if (LBT.phase !== 'mise') return repondre(res, 409, { erreur: 'Les mises sont fermees.' });
    const mise = sous(Number(body.mise) || 0);
    if (mise && !(mise >= LBT_MIN && mise <= LBT_MAX)) return repondre(res, 400, { erreur: 'Mise entre 1 € et 5 000 €.' });
    const delta = sous(mise - p.mise);
    if (delta > compte.solde + 1e-9) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
    compte.solde = sous(compte.solde - delta); p.mise = mise; soldeAuSiege(compte); Carnet.enregistrer(compte);
    if (mise && !LBT.echeance) LBT.echeance = Date.now() + LBT_MISE_MS;
    if (!LBT.places.some(q => q && q.mise > 0)) LBT.echeance = 0;
    lbtPousser({ qui: 'mise', place: moi, mise });
    if (res.__suivi) res.__suivi.nomJeu = 'Live Blackjack';
    return repondre(res, 200, lbtEtat(compte, body.depuis));
  }
  if (route === '/api/lbt-assurance') {
    if (LBT.phase !== 'assurance' || !p.mains.length || p.assurance) return repondre(res, 409, { erreur: 'Pas d\'assurance possible.' });
    if (body.oui) { const a = sous(p.mains[0].mise / 2); if (a <= compte.solde) { compte.solde = sous(compte.solde - a); p.assurance = a; soldeAuSiege(compte); Carnet.enregistrer(compte); } }
    p.assuranceVue = true;
    if (lbtJoueurs().every(i => LBT.places[i].assuranceVue)) { lbtJoueurs().forEach(i => LBT.places[i].assuranceVue = false); lbtApresDonne(); }
    return repondre(res, 200, lbtEtat(compte, body.depuis));
  }
  if (route === '/api/lbt-action') {
    const a = LBT.active;
    if (LBT.phase !== 'joueurs' || !a || a.place !== moi) return repondre(res, 409, { erreur: 'Ce n\'est pas votre tour.' });
    const m = p.mains[a.main], action = String(body.action || ''), peut = lbtPeut(compte);
    if (action === 'tirer') {
      const c = lbtTirer(); m.cartes.push(c); lbtPousser({ qui: 'j', place: moi, main: a.main, c });
      if (compter(m.cartes) >= 21) { m.fini = true; lbtSuivant(); } else LBT.echeance = Date.now() + LBT_TOUR_MS;
    } else if (action === 'rester') { m.fini = true; lbtSuivant(); }
    else if (action === 'doubler') {
      if (!peut.doubler) return repondre(res, 400, { erreur: 'Impossible de doubler.' });
      compte.solde = sous(compte.solde - m.mise); m.mise = sous(m.mise * 2); m.double = true; p.mise = sous(p.mains.reduce((s, x) => s + x.mise, 0));
      const c = lbtTirer(); m.cartes.push(c); lbtPousser({ qui: 'j', place: moi, main: a.main, c, double: true });
      m.fini = true; lbtSuivant();
    } else if (action === 'split') {
      if (!peut.split) return repondre(res, 400, { erreur: 'Impossible de spliter.' });
      compte.solde = sous(compte.solde - m.mise);
      const as = m.cartes[0].h === 'A';
      const m2 = { cartes: [m.cartes.pop()], mise: m.mise, splitAs: as }; m.splitAs = as;
      p.mains.push(m2); p.mise = sous(m.mise * 2); lbtPousser({ qui: 'split', place: moi });
      const c = lbtTirer(); m.cartes.push(c); lbtPousser({ qui: 'j', place: moi, main: 0, c });
      if (as || compter(m.cartes) >= 21) { m.fini = true; lbtSuivant(); } else LBT.echeance = Date.now() + LBT_TOUR_MS;
    } else return repondre(res, 400, { erreur: 'Action inconnue.' });
    soldeAuSiege(compte); Carnet.enregistrer(compte);
    if (res.__suivi) res.__suivi.nomJeu = 'Live Blackjack';
    return repondre(res, 200, lbtEtat(compte, body.depuis));
  }
  return repondre(res, 404, { erreur: 'route inconnue' });
}

const NOMS_ROUTES = [
  ['peche', 'Pêche avec Jeffrey', 'peche'], ['block', 'Block', 'jeu'], ['poulet', 'Le Poulet', 'jeu'], ['mines', 'Mines', 'jeu'], ['moles', 'Moles', 'jeu'], ['croco', 'Crocodino', 'jeu'], ['rlive', 'Roulette Live', 'jeu'], ['joker', 'Rich Joker', 'jeu'], ['plinko', 'Plinko', 'jeu'],
  ['kroad', 'Koala Road', 'jeu'], ['thimbles', 'Thimbles', 'jeu'], ['tower', 'Tower Rush', 'jeu'], ['pont', 'Pont de Cristal', 'jeu'],
  ['penalty', 'Le penalty', 'jeu'], ['periph', 'Le périph', 'jeu'], ['bois', 'Le périph', 'jeu'],
  ['miser', 'Blackjack', 'jeu'], ['action', 'Blackjack', 'jeu'], ['roulette', 'Roulette', 'jeu'],
  ['slot', 'Slot Games', 'jeu'], ['avion', 'Crash Game', 'jeu'], ['lbt', 'Live Blackjack', 'jeu'], ['lbe', 'Live Blackjack Ethan', 'jeu'], ['lbj', 'Live Blackjack', 'jeu'], ['code', 'Code promo', 'promo'], ['razzia', 'Razzia', 'razzia'], ['table-offrir', 'Cadeau à un joueur', 'cadeau']];
function nomDeRoute(route) {
  const r = route.slice(5);
  for (const [p, nom, type] of NOMS_ROUTES) if (r === p || r.startsWith(p + '-') || r.startsWith(p)) return { nom, type };
  return { nom: 'Casino', type: 'jeu' };
}
function noterMouvement(compte, nom, type, m, statut) {
  m = sous(m); if (!m) return;
  if (!Array.isArray(compte.tx)) compte.tx = [];
  const t = Date.now(), d = compte.tx[0];
  // les petits mouvements repetes (poissons, plinko...) se cumulent sur une seule ligne
  if (!statut && d && !d.statut && d.jeu === nom && d.type === type && (d.m > 0) === (m > 0) && t - d.t < 30 * 60000) { d.m = sous(d.m + m); d.t = t; }
  else { compte.tx.unshift(statut ? { t, type, jeu: nom, m, statut } : { t, type, jeu: nom, m }); if (compte.tx.length > 60) compte.tx.length = 60; }
  if (type === 'jeu' && m < 0) compte.points = (compte.points | 0) + Math.round(-m * 100);
  if (type === 'jeu' && m >= 5) { GROS_GAINS.unshift({ id: ++grosGainsId, pseudo: compte.pseudo, jeu: nom, m, t }); if (GROS_GAINS.length > 15) GROS_GAINS.length = 15; }
}
/* ce que le joueur est en train de faire, d'apres la derniere route qu'il utilise */
function activiteDe(c, route) {
  const r = route.slice(5);
  if (['moi', 'salon', 'accueil', 'code', 'bannir', 'supprimer-compte', 'modifier-solde', 'gains-effacer', 'perso', 'retrait', 'quitter', 'roulette-quitter'].includes(r)) return null;
  if (r === 'etat' || r === 'asseoir' || r === 'miser' || r === 'action' || r.startsWith('table-')) { const i = siegeDe(c); return i && i.table && i.table.jeu === 'poker' ? 'joue au Poker' : 'joue au Blackjack'; }
  if (r.startsWith('poker')) return 'joue au Poker';
  if (r.startsWith('roulette')) return 'joue à la Roulette';
  if (r === 'peche') return 'pêche avec Jeffrey';
  if (r.startsWith('bois')) return 'joue au Périph (Bois)';
  const n = nomDeRoute(route); return n.nom === 'Casino' ? null : 'joue à ' + n.nom;
}
function suivreSolde(res) {
  const s = res.__suivi; if (!s) return; res.__suivi = null;
  const c = s.compte, apres = c.solde;
  if (typeof c.soldeSuivi !== 'number') c.soldeSuivi = s.avant;
  const hors = sous(s.avant - c.soldeSuivi);
  if (hors) {
    let nom = c.soldeHorsNom || 'Casino', type = c.soldeHorsNom ? 'admin' : 'jeu';
    if (!c.soldeHorsNom) { const info = siegeDe(c); if (info && info.table) nom = info.table.jeu === 'poker' ? 'Poker' : 'Blackjack'; else if (c.tableRoulette) nom = 'Roulette'; }
    noterMouvement(c, nom, type, hors);
  }
  c.soldeHorsNom = null;
  const delta = sous(apres - s.avant);
  if (delta && !s.deja) { const n = s.nomJeu ? { nom: s.nomJeu, type: 'jeu' } : nomDeRoute(s.route); noterMouvement(c, n.nom, n.type, delta); }
  c.soldeSuivi = apres;
}

function repondre(res, code, objet) {
  suivreSolde(res);
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

/* la page est lue et compressee une seule fois (elle charge bien plus vite) */
let PAGE = null;
function servirFichier(res, chemin, req) {
  const envoyerPage = () => {
    const gz = /\bgzip\b/.test((req && req.headers['accept-encoding']) || '');
    const h = { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache', 'ETag': PAGE.etag, 'Vary': 'Accept-Encoding' };
    if (req && req.headers['if-none-match'] === PAGE.etag) { res.writeHead(304, h); res.end(); return; }
    if (gz) h['Content-Encoding'] = 'gzip';
    res.writeHead(200, h); res.end(gz ? PAGE.gz : PAGE.brut);
  };
  if (PAGE) return envoyerPage();
  fs.readFile(chemin, (err, contenu) => {
    if (err) { res.writeHead(404); res.end('Introuvable'); return; }
    PAGE = { brut: contenu, gz: require('zlib').gzipSync(contenu, { level: 9 }),
             etag: '"' + crypto.createHash('sha1').update(contenu).digest('hex').slice(0, 16) + '"' };
    envoyerPage();
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
    let activite = null;
    for (const c of comptes.values()) if (c.pseudoBas === j.pseudoBas && enLigne && c.activite && maintenant - c.activite.t < 90000) activite = c.activite.nom;
    return { pseudo: j.pseudo, pseudoBas: j.pseudoBas, creeLe: j.creeLe || null, vuLe: vuLe, enLigne: enLigne, activite: activite };
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

const ICONE_180 = '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';
const ICONE_512 = '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1S227LrUDOs+SimEpJpAGkiikoQm4VBoEggJiDIKAYQAKpCEURhJQpNwSGQjjMJtQjgQRvI9SxbneT0Ldwogo9DI3YQQaeQWGYWRgBogoZFbpJFbJCAjG5oEUEEFiShggxxQAUPAblIYDcN6vdrfX3Tde971pl/71Z/86M+848zkygtf/dwrz36rm06PHDue2K/WBEsBQRBRETCggIAxhEZAQAUbFAgjpRRL12np18P+zf3V/tJJd/TkiZPn7jt55t7pkVOUrWv79dsX9556+dozz1946flXXn3xwuWLVy5eunbt6s1r13dv3NzfW65X66GvQ60D1PmkO7K9OHH8yLkzp954/70P/8ADb37r+bc+8saHzh49OV/3uy9ffuXpV5979saly6TOF/PGUmqtEPAACoHQhCaEUQgkHAiNDWSj1jSgoBZRRCQcUkaagIxUAohNEg4UmhCIUoqlWPu6v7dcLZfdpJw4fezM2TNHj55e1e1nr+abr+w+/uyV5567/MJzl55/8dJzL199+eKNvWt7sIQ1BIQOppPtrdOnjt5z9vg9Z07fc8+ZNz547/3n73vwgXNvOHf8/lM7546U0u1x8+K1iy9dv3xhvbc76bqt7e3ZYlG6SZI6hEawAQLKoRABG0ayIUkYSQABgRBNAqWUYVjv792cTmbH3/AmTjz8xa9f+d9+85P/72//yQvPvMhktrW9la6rQDIMAVGQhFRSkwCRUYAQDiUQCIQAoozCSBJuEcIdEhJGIncIo/B9340szvO9IjSRUWjkbkKINPLdSKM0CXdSGtmQQwIaIEpQARUCiIIKKI0KqAmICnU6KZDr12+yu/fG8/f9i1/9yX/xT3/0kVPDy098+eVnngzDYrENpfYDioKgSKMIykhAJdymARFUUAQMqIhAJAxDHYahppJqyrSbL3aOHztz9si5e8qJU/1ka3evv37l+qsvX3vx5evPvXLtpVevvXLx6qXLN69e27u5v1qu10NdF7I1m5w+eeyB+848ev4Nb3n0gYff9Maz545vuVpdfOH6C09eefmZ3esXh35tmXTTeek6G0YWtQACgoaQkKBCEiAJTQJIY0NCUtNQawCluAECgoaRICCBMFIBpRGTcEAsxgBJTAjZqBlqv6YOs25y5MixY6fPzU6dy86x3b67eHH5zLNXH3vq0pefuvTNZy48++Lly5ev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';

const serveur = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://x');
  const route = url.pathname;

  /* ---------------- application (ecran d'accueil du telephone) ---------------- */
  if (route === '/manifest.webmanifest') {
    res.writeHead(200, { 'Content-Type': 'application/manifest+json; charset=utf-8', 'Cache-Control': 'no-cache' });
    res.end(JSON.stringify({ name: 'Casino Messina', short_name: 'Messina', start_url: '/', scope: '/', display: 'standalone',
      orientation: 'portrait', background_color: '#0d0b1a', theme_color: '#0d0b1a',
      icons: [{ src: '/icone-180.png', sizes: '180x180', type: 'image/png' }, { src: '/icone-512.png', sizes: '512x512', type: 'image/png', purpose: 'any' }] }));
    return;
  }
  if (route === '/icone-180.png' || route === '/icone-512.png' || route === '/apple-touch-icon.png' || route === '/apple-touch-icon-precomposed.png') {
    res.writeHead(200, { 'Content-Type': 'image/png', 'Cache-Control': 'public, max-age=86400' });
    res.end(Buffer.from(route === '/icone-512.png' ? ICONE_512 : ICONE_180, 'base64'));
    return;
  }

  /* ---------------- diagnostic du croupier LiveAvatar (admin) ---------------- */
  if (route === '/diag-croupier') {
    if (url.searchParams.get('code') !== 'exclusionfdp') { res.writeHead(404); res.end('Introuvable'); return; }
    const CLE = (process.env.LIVEAVATAR_API_KEY || '').trim(), rapport = {
      variables: { LIVEAVATAR_API_KEY: CLE ? 'presente (' + CLE.length + ' caracteres)' : 'MANQUANTE',
        LIVEAVATAR_AVATAR_ID: process.env.LIVEAVATAR_AVATAR_ID || 'MANQUANTE',
        LIVEAVATAR_VOICE_AGENT_ID: (process.env.LIVEAVATAR_VOICE_AGENT_ID || '').trim() || 'MANQUANTE OU VIDE (obligatoire)',
        autres_variables_liveavatar_trouvees: Object.keys(process.env).filter(k => /LIVE.?AVATAR|VOICE/i.test(k)),
        requete_envoyee: { mode: 'FULL', avatar_id: (process.env.LIVEAVATAR_AVATAR_ID || '').trim() || null, voice_agent: { id: (process.env.LIVEAVATAR_VOICE_AGENT_ID || '').trim() || null } },
        LIVEAVATAR_SANDBOX: process.env.LIVEAVATAR_SANDBOX || 'absente' },
      requete_token_exacte: { methode: 'POST', url: 'https://api.liveavatar.com/v1/sessions/token', entetes: { 'X-API-KEY': '***masque***', 'Content-Type': 'application/json', 'Accept': 'application/json' }, json: croupierDemande() },
      note_doc_sandbox: 'Doc officielle : en sandbox (is_sandbox=true) seul l\'avatar Wayne dd73ea75-1218-4ef3-92ce-606d5f7fbc0a est autorise.',
      derniere_session_reussie: CROUPIER_OK, derniere_erreur_serveur: CROUPIER_ERREUR, derniere_erreur_telephone: CROUPIER_ERREUR_TEL };
    if (url.searchParams.get('tester') === '1' && CLE) {
      try {
        const r = await fetch('https://api.liveavatar.com/v1/sessions/token', { method: 'POST', headers: { 'X-API-KEY': CLE.trim(), 'Content-Type': 'application/json', 'Accept': 'application/json' }, body: JSON.stringify(croupierDemande()) });
        const txt = await r.text(); let corps; try { corps = croupierMasquer(JSON.parse(txt)); } catch (e) { corps = txt.slice(0, 3000); }
        rapport.test_token_maintenant = { status_http: r.status, reponse_liveavatar_complete: corps };
      } catch (e) { rapport.test_token_maintenant = { erreur_reseau: String(e && e.message) }; }
    }
    try {
      if (CLE) {
        const r = await fetch('https://api.liveavatar.com/v1/avatars?page_size=100', { headers: { 'X-API-KEY': CLE, 'Accept': 'application/json' } });
        const x = await r.json().catch(() => ({}));
        rapport.cle_api = r.ok ? 'ACCEPTEE par LiveAvatar' : 'REFUSEE par LiveAvatar (statut ' + r.status + ')';
        rapport.mes_avatars = ((x.data && x.data.results) || []).map(a => ({ id: a.id, nom: a.name, statut: a.status }));
      }
      const r2 = await fetch('https://api.liveavatar.com/v1/avatars/public?page_size=100');
      const y = await r2.json().catch(() => ({}));
      rapport.avatars_publics_graham = ((y.data && y.data.results) || []).filter(a => /graham/i.test(a.name || '')).map(a => ({ id: a.id, nom: a.name, statut: a.status }));
      const av = process.env.LIVEAVATAR_AVATAR_ID;
      if (av) rapport.avatar_id_reconnu = [...(rapport.mes_avatars || []), ...((y.data && y.data.results) || [])].some(a => a.id === av) ? 'OUI' : 'NON (cet identifiant ne correspond a aucun avatar trouve)';
    } catch (e) { rapport.erreur_reseau = String(e && e.message); }
    res.writeHead(200, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' });
    res.end(JSON.stringify(rapport, null, 2)); return;
  }

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
    res.__suivi = { compte, route, avant: compte.solde };
    { const a = activiteDe(compte, route); if (a) compte.activite = { nom: a, t: Date.now() }; }

    // --- l'accueil : les vrais gros gains recents de tout le casino ---
    if (route === '/api/accueil') {
      return repondre(res, 200, { gains: GROS_GAINS.slice(0, 10).map(g => ({ pseudo: g.pseudo, jeu: g.jeu, m: g.m })) });
    }

    // --- effacer un gros gain (ou tous ceux d'un joueur) du bandeau de l'accueil : code KQ8 ---
    if (route === '/api/gains-effacer' && req.method === 'POST') {
      if (String(body.code || '').trim().toLowerCase().replace(/\s+/g, '') !== 'kq8') return repondre(res, 403, { erreur: 'Code invalide.' });
      const qui = String(body.pseudo || '');
      for (let i = GROS_GAINS.length - 1; i >= 0; i--) {
        if (qui ? GROS_GAINS[i].pseudo === qui : GROS_GAINS[i].id === Number(body.id)) GROS_GAINS.splice(i, 1);
      }
      return repondre(res, 200, { ok: true, gains: GROS_GAINS.slice(0, 10) });
    }

    // --- retrait (argent fictif) : le solde baisse, rien d'autre ne se passe.
    // Seuls le montant et les 4 derniers chiffres arrivent ici : le reste de
    // la carte ne quitte jamais la page. ---
    if (route === '/api/retrait' && req.method === 'POST') {
      const montant = sous(Number(body.montant) || 0);
      const fin = /^\d{4}$/.test(String(body.fin || '')) ? String(body.fin) : '????';
      if (!(montant >= 1)) return repondre(res, 400, { erreur: 'Retrait minimum : 1,00 €.' });
      if (montant > compte.solde) return repondre(res, 400, { erreur: 'Tu ne peux pas retirer plus que ton solde.' });
      compte.solde = sous(compte.solde - montant);
      noterMouvement(compte, 'Retrait vers carte •••• ' + fin, 'retrait', -montant, 'En traitement · 48 h');
      res.__suivi.deja = true;
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, montant, solde: compte.solde });
    }

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
          type: 'humain', jeton: compte.jetonRef, nom: compte.pseudo, soldeRef: compte.solde,
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
        type: 'humain', jeton: compte.jetonRef, nom: compte.pseudo, soldeRef: compte.solde,
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
        const prises = tableRoulette.places.filter(Boolean).map(x => x.couleur);
        const couleur = [0, 1, 2, 3, 4, 5, 6].find(k => !prises.includes(k)) || 0;
        tableRoulette.places[i] = { jeton: compte.jetonRef, nom: compte.pseudo, couleur, mises: {}, dernierGain: 0, derniereMiseTotale: 0, dernieresMises: {} };
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

      const dejaMise = Object.values(p.mises).reduce((a, b) => a + b, 0);
      if (dejaMise + v > 10000 + 1e-9) return repondre(res, 400, { erreur: 'Mise maximum : 10 000 € par tour.' });
      compte.solde = sous(compte.solde - v);
      soldeAuSiege(compte);
      p.mises[zone.id] = sous((p.mises[zone.id] || 0) + v);
      toucheRoulette();
      return repondre(res, 200, etatRoulette(compte.jetonRef));
    }

    // --- plusieurs mises d'un coup (bouton Repeter / Doubler) ---
    if (route === '/api/roulette-lot' && req.method === 'POST') {
      const p = tableRoulette.places.find(x => x && x.jeton === compte.jetonRef);
      if (!p) return repondre(res, 409, { erreur: 'pas a table' });
      if (tableRoulette.phase !== 'mise') return repondre(res, 409, { erreur: 'trop tard' });
      const lot = body.mises && typeof body.mises === 'object' ? body.mises : {};
      let total = 0; const propre = {};
      for (const id of Object.keys(lot)) {
        const zone = trouverZoneRoulette(id), m = sous(Number(lot[id]));
        if (!zone || !isFinite(m) || m < 0.01) return repondre(res, 400, { erreur: 'mise invalide' });
        propre[id] = m; total = sous(total + m);
      }
      if (!total) return repondre(res, 400, { erreur: 'rien a miser' });
      const dejaMise = Object.values(p.mises).reduce((a, b) => a + b, 0);
      if (dejaMise + total > 10000 + 1e-9) return repondre(res, 400, { erreur: 'Mise maximum : 10 000 € par tour.' });
      if (total > compte.solde + 1e-9) return repondre(res, 400, { erreur: 'solde insuffisant' });
      compte.solde = sous(compte.solde - total);
      soldeAuSiege(compte);
      for (const id of Object.keys(propre)) p.mises[id] = sous((p.mises[id] || 0) + propre[id]);
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
      majSoldeCompte(p);                      // le vrai solde, pas une vieille copie
      // on change sa mise : l'ancienne est rendue avant de poser la nouvelle
      if (p.mains[0].mise > 0) { p.solde = sous(p.solde + p.mains[0].mise); p.mains[0].mise = 0; majSoldeCompte(p); }

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
      majSoldeCompte(p);

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
      majSoldeCompte(p); majSoldeCompte(cible);
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

    if (route === '/api/block-etat' && req.method === 'POST') {
      if (!compte.block || body.nouvelle) bkNouvelle(compte);
      return repondre(res, 200, bkVue(compte));
    }
    if (route === '/api/block-poser' && req.method === 'POST') {
      const b = compte.block; if (!b) return repondre(res, 409, { erreur: 'Aucune partie.' });
      const i = Number(body.i), r = Number(body.r), c = Number(body.c);
      const p = b.pieces[i];
      if (!p || !Number.isInteger(r) || !Number.isInteger(c) || !bkPeut(b.g, p.f, r, c)) return repondre(res, 200, bkVue(compte, { refuse: true }));
      const avantCases = b.g.reduce((n, l) => n + l.filter(v => v).length, 0);
      const o = bkPoserSur(b.g, p.f, r, c, p.col);
      b.g = o.g; b.pieces[i] = null; b.coups++;
      const nl = o.lignes.length + o.cols.length;
      let pts = p.f.length, gain = 0, vide = false, tropTot = false;
      if (nl) { b.combo++; b.sansExplo = 0; pts += o.efface * 10 * Math.max(1, nl - 0) + (b.combo > 1 ? b.combo * 20 : 0); }
      else { b.sansExplo++; if (b.sansExplo >= 3) b.combo = 0; }
      if (nl && !b.g.some(l => l.some(v => v))) {
        vide = true; pts += 300;
        const jour = new Date().toISOString().slice(0, 10);
        if (compte.blockJour !== jour) { compte.blockJour = jour; compte.blockAuj = 0; }
        // anti-triche : pas de gain sur un plateau presque vide en debut de partie (sinon on relance jusqu'a avoir les bonnes pieces)
        if (b.coups < 4 || avantCases < 6) tropTot = true;
        else if ((compte.blockAuj | 0) + BLOCK_GAIN <= BLOCK_MAX_JOUR) {
          gain = BLOCK_GAIN; compte.blockAuj = (compte.blockAuj | 0) + BLOCK_GAIN;
          compte.solde = sous(compte.solde + BLOCK_GAIN); compte.blockVides = (compte.blockVides | 0) + 1;
          soldeAuSiege(compte);
        }
      }
      b.score += pts;
      if (b.score > (compte.blockBest | 0)) compte.blockBest = b.score;
      if (b.pieces.every(x => !x)) b.pieces = bkLot(b.g);
      Carnet.enregistrer(compte);
      return repondre(res, 200, bkVue(compte, { lignes: o.lignes, cols: o.cols, pts, gain, vide, tropTot }));
    }
    if (route === '/api/peche' && req.method === 'POST') {
      const jour = new Date().toISOString().slice(0, 10);
      if (compte.pecheJour !== jour) { compte.pecheJour = jour; compte.pecheAuj = 0; }
      if (compte.pecheAuj >= PECHE_MAX_JOUR) {
        return repondre(res, 200, { solde: compte.solde, poissons: compte.poissons, plafond: true });
      }
      compte.pecheAuj = compte.pecheAuj + 1;
      compte.solde    = sous(compte.solde + 1);
      compte.poissons = compte.poissons + 1;
      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
      Carnet.enregistrer(compte);
      return repondre(res, 200, { solde: compte.solde, poissons: compte.poissons, restant: PECHE_MAX_JOUR - compte.pecheAuj });
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
      if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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
        if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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
      if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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
    if (route === '/api/periph-acheter-voiture' && req.method === 'POST' && body.modele === 'hybride') {
      if (compte.voitureHybride) return repondre(res, 409, { erreur: 'Vous avez deja cette voiture.' });
      if (compte.periph) return repondre(res, 409, { erreur: 'Terminez votre course avant d\'aller a la boutique.' });
      if (compte.solde < PRIX_VOITURE_HYBRIDE) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      compte.solde = sous(compte.solde - PRIX_VOITURE_HYBRIDE);
      compte.voitureHybride = true;
      if (res.__suivi) res.__suivi.deja = true;
      noterMouvement(compte, 'Boutique : GT Hybride', 'cadeau', -PRIX_VOITURE_HYBRIDE);
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, solde: compte.solde, voitureHybride: true });
    }
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
      if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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
      const vitesseMax = vmaxPeriph(course.voiture);
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
      if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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

      const voitureDemandee = choisirVoiture(compte, body.voiture);
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
          const vmax = course ? vmaxPeriph(course.voiture) : VITESSE_MAX_PERIPH;
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
      const vitesseMax = vmaxPeriph(course.voiture);
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
       LE POULET
       ---------------------------------------------------------------
       25 cloches, de 1 a 24 os caches dessous. Les os sont tires ICI et
       ne quittent le serveur qu'a la fin de la manche. Cote :
       0,99 x (cases restantes / (cases restantes - os)) a chaque poulet,
       soit 0,99 x C(25,k) / C(25-os,k). Mini x1,03 (1 os), maxi x24,75
       (24 os). Gain plafonne a 10 000 EUR : encaisse d'office.
       =============================================================== */
    if (route === '/api/poulet-demarrer' && req.method === 'POST') {
      if (compte.poulet) return repondre(res, 409, { erreur: 'Une partie est deja en cours.' });
      const mise = sous(Number(body.mise) || 0);
      const nbOs = Number(body.os) | 0;
      if (!(nbOs >= 1 && nbOs <= 24)) return repondre(res, 400, { erreur: 'Choisissez entre 1 et 24 os.' });
      if (!(mise >= 0.20)) return repondre(res, 400, { erreur: 'Mise minimum : 0,20 €.' });
      if (mise > 1000)     return repondre(res, 400, { erreur: 'Mise maximum : 1 000 €.' });
      if (mise > compte.solde) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      const cases = []; for (let i = 0; i < 25; i++) cases.push(i);
      for (let i = 24; i > 0; i--) { const j = crypto.randomInt(i + 1); const t = cases[i]; cases[i] = cases[j]; cases[j] = t; }
      compte.solde = sous(compte.solde - mise);
      compte.poulet = { mise: mise, nbOs: nbOs, os: cases.slice(0, nbOs), ouverts: [] };
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, mise: mise, os: nbOs, solde: compte.solde });
    }

    if (route === '/api/poulet-ouvrir' && req.method === 'POST') {
      const p = compte.poulet;
      if (!p) return repondre(res, 409, { erreur: 'Aucune partie en cours.' });
      const c = Number(body.case);
      if (!(Number.isInteger(c) && c >= 0 && c < 25)) return repondre(res, 400, { erreur: 'Case inconnue.' });
      if (p.ouverts.includes(c)) return repondre(res, 400, { erreur: 'Case deja ouverte.' });
      if (p.os.includes(c)) {
        compte.poulet = null;
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, os: true, case: c, tousLesOs: p.os, perdu: p.mise, solde: compte.solde });
      }
      p.ouverts.push(c);
      const k = p.ouverts.length;
      const mult = pouletMult(p.nbOs, k);
      const gain = Math.min(10000, sous(p.mise * mult));
      if (k >= 25 - p.nbOs || gain >= 10000) {          // tout trouve, ou plafond : on encaisse d\'office
        compte.solde = sous(compte.solde + gain);
        compte.poulet = null;
        soldeAuSiege(compte);
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, os: false, case: c, mult: mult, gain: gain, fini: true, tousLesOs: p.os, solde: compte.solde });
      }
      return repondre(res, 200, { ok: true, os: false, case: c, mult: mult, gain: gain, suivant: pouletMult(p.nbOs, k + 1), solde: compte.solde });
    }

    if (route === '/api/poulet-encaisser' && req.method === 'POST') {
      const p = compte.poulet;
      if (!p) return repondre(res, 409, { erreur: 'Aucune partie en cours.' });
      if (!p.ouverts.length) return repondre(res, 400, { erreur: 'Trouvez au moins un poulet avant d\'encaisser.' });
      const mult = pouletMult(p.nbOs, p.ouverts.length);
      const gain = Math.min(10000, sous(p.mise * mult));
      compte.solde = sous(compte.solde + gain);
      compte.poulet = null;
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, gain: gain, mult: mult, tousLesOs: p.os, solde: compte.solde });
    }

    /* ===============================================================
       MINES : 25 cases, de 1 a 24 mines. Meme calcul que le Poulet
       (0,99 x C(25,k) / C(25-mines,k)). Mines tirees et gardees ICI.
       =============================================================== */
    /* ===============================================================
       MOLES : 7 trous, de 1 a 6 taupes. A chaque coup de marteau les
       taupes sont replacees au hasard ICI ; toucher une taupe = gagne.
       Cote apres k coups reussis : 0,98 x (7 / taupes)^k. 10 coups max.
       =============================================================== */
    /* ===============================================================
       CROCODINO : 20 dents, de 1 a 19 dents rouges tirees ICI.
       Cote apres k dents blanches : 0,99 x C(20,k) / C(20-rouges,k).
       Gain maxi 10 000 EUR (encaisse d'office).
       =============================================================== */
    if (route === '/api/croco-demarrer' && req.method === 'POST') {
      if (compte.croco) return repondre(res, 409, { erreur: 'Une partie est deja en cours.' });
      const mise = sous(Number(body.mise) || 0);
      const nb = Number(body.rouges) | 0;
      if (!(nb >= 1 && nb <= 19)) return repondre(res, 400, { erreur: 'Choisissez entre 1 et 19 dents rouges.' });
      if (!(mise >= 0.20)) return repondre(res, 400, { erreur: 'Mise minimum : 0,20 €.' });
      if (mise > 1000)     return repondre(res, 400, { erreur: 'Mise maximum : 1 000 €.' });
      if (mise > compte.solde) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      const d = []; for (let i = 0; i < 20; i++) d.push(i);
      for (let i = 19; i > 0; i--) { const j = crypto.randomInt(i + 1); const t = d[i]; d[i] = d[j]; d[j] = t; }
      compte.solde = sous(compte.solde - mise);
      compte.croco = { mise: mise, nb: nb, rouges: d.slice(0, nb), ouverts: [] };
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, mise: mise, rouges: nb, suivant: crocoMult(nb, 1), solde: compte.solde });
    }
    if (route === '/api/croco-ouvrir' && req.method === 'POST') {
      const p = compte.croco;
      if (!p) return repondre(res, 409, { erreur: 'Aucune partie en cours.' });
      const c = Number(body.dent);
      if (!(Number.isInteger(c) && c >= 0 && c < 20)) return repondre(res, 400, { erreur: 'Dent inconnue.' });
      if (p.ouverts.includes(c)) return repondre(res, 400, { erreur: 'Dent deja choisie.' });
      if (p.rouges.includes(c)) {
        compte.croco = null;
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, rouge: true, dent: c, toutes: p.rouges, perdu: p.mise, solde: compte.solde });
      }
      p.ouverts.push(c);
      const k = p.ouverts.length;
      const mult = crocoMult(p.nb, k);
      const gain = Math.min(10000, sous(p.mise * mult));
      if (k >= 20 - p.nb || gain >= 10000) {
        compte.solde = sous(compte.solde + gain);
        compte.croco = null;
        soldeAuSiege(compte);
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, rouge: false, dent: c, mult: mult, gain: gain, fini: true, toutes: p.rouges, solde: compte.solde });
      }
      return repondre(res, 200, { ok: true, rouge: false, dent: c, mult: mult, gain: gain, suivant: crocoMult(p.nb, k + 1), solde: compte.solde });
    }
    if (route === '/api/croco-encaisser' && req.method === 'POST') {
      const p = compte.croco;
      if (!p) return repondre(res, 409, { erreur: 'Aucune partie en cours.' });
      if (!p.ouverts.length) return repondre(res, 400, { erreur: 'Choisissez au moins une dent avant d\'encaisser.' });
      const mult = crocoMult(p.nb, p.ouverts.length);
      const gain = Math.min(10000, sous(p.mise * mult));
      compte.solde = sous(compte.solde + gain);
      compte.croco = null;
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, gain: gain, mult: mult, toutes: p.rouges, solde: compte.solde });
    }
    if (route === '/api/croco-etat' && req.method === 'POST') {
      const p = compte.croco;
      if (!p) return repondre(res, 200, { ok: true, enCours: false, solde: compte.solde });
      return repondre(res, 200, { ok: true, enCours: true, mise: p.mise, rouges: p.nb, ouverts: p.ouverts,
        mult: p.ouverts.length ? crocoMult(p.nb, p.ouverts.length) : 0, suivant: crocoMult(p.nb, p.ouverts.length + 1), solde: compte.solde });
    }

    if (route === '/api/moles-demarrer' && req.method === 'POST') {
      if (compte.moles) return repondre(res, 409, { erreur: 'Une partie est deja en cours.' });
      const mise = sous(Number(body.mise) || 0);
      const nb = Number(body.taupes) | 0;
      if (!(nb >= 1 && nb <= 6)) return repondre(res, 400, { erreur: 'Choisissez entre 1 et 6 taupes.' });
      if (!(mise >= 0.10)) return repondre(res, 400, { erreur: 'Mise minimum : 0,10 €.' });
      if (mise > 1000)     return repondre(res, 400, { erreur: 'Mise maximum : 1 000 €.' });
      if (mise > compte.solde) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      compte.solde = sous(compte.solde - mise);
      compte.moles = { mise: mise, nb: nb, k: 0 };
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, mise: mise, taupes: nb, suivant: molesMult(nb, 1), solde: compte.solde });
    }
    if (route === '/api/moles-taper' && req.method === 'POST') {
      const p = compte.moles;
      if (!p) return repondre(res, 409, { erreur: 'Aucune partie en cours.' });
      const c = Number(body.trou);
      if (!(Number.isInteger(c) && c >= 0 && c < 7)) return repondre(res, 400, { erreur: 'Trou inconnu.' });
      const trous = [0, 1, 2, 3, 4, 5, 6];
      for (let i = 6; i > 0; i--) { const j = crypto.randomInt(i + 1); const t = trous[i]; trous[i] = trous[j]; trous[j] = t; }
      const taupes = trous.slice(0, p.nb).sort();
      if (!taupes.includes(c)) {
        compte.moles = null;
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, touche: false, trou: c, taupes: taupes, perdu: p.mise, solde: compte.solde });
      }
      p.k++;
      const mult = molesMult(p.nb, p.k);
      const gain = Math.min(10000, sous(p.mise * mult));
      if (p.k >= 10 || gain >= 10000) {
        compte.solde = sous(compte.solde + gain);
        compte.moles = null;
        soldeAuSiege(compte);
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, touche: true, trou: c, taupes: taupes, mult: mult, gain: gain, fini: true, solde: compte.solde });
      }
      return repondre(res, 200, { ok: true, touche: true, trou: c, taupes: taupes, mult: mult, gain: gain, suivant: molesMult(p.nb, p.k + 1), solde: compte.solde });
    }
    if (route === '/api/moles-encaisser' && req.method === 'POST') {
      const p = compte.moles;
      if (!p) return repondre(res, 409, { erreur: 'Aucune partie en cours.' });
      if (!p.k) return repondre(res, 400, { erreur: 'Touchez au moins une taupe avant d\'encaisser.' });
      const mult = molesMult(p.nb, p.k);
      const gain = Math.min(10000, sous(p.mise * mult));
      compte.solde = sous(compte.solde + gain);
      compte.moles = null;
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, gain: gain, mult: mult, solde: compte.solde });
    }
    if (route === '/api/moles-etat' && req.method === 'POST') {
      const p = compte.moles;
      if (!p) return repondre(res, 200, { ok: true, enCours: false, solde: compte.solde });
      return repondre(res, 200, { ok: true, enCours: true, mise: p.mise, taupes: p.nb, k: p.k,
        mult: p.k ? molesMult(p.nb, p.k) : 0, suivant: molesMult(p.nb, p.k + 1), solde: compte.solde });
    }

    /* ===== RICH JOKER ===== */
    if (route === '/api/joker-tourner' && req.method === 'POST') {
      const mise = sous(Number(body.mise) || 0);
      if (RJ_MISES.indexOf(mise) < 0) return repondre(res, 400, { erreur: 'Mise invalide.' });
      if (mise > compte.solde) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      compte.solde = sous(compte.solde - mise);
      const t = rjTourner(mise);
      if (t.gain > 0) compte.solde = sous(compte.solde + t.gain);
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      t.solde = compte.solde;
      return repondre(res, 200, Object.assign({ ok: true }, t));
    }

    /* ===== ROULETTE LIVE ===== */
    if (route === '/api/rlive-etat' && req.method === 'POST') {
      const r = compte.rlive && compte.rlive.tour === rlive.tour ? compte.rlive : null;
      const prec = compte.rlive && compte.rlive.paye && compte.rlive.tour === rlive.tour ? compte.rlive : null;
      return repondre(res, 200, { ok: true, tour: rlive.tour, phase: rlive.phase, maintenant: Date.now(), debut: rlive.debut, echeance: rlive.echeance,
        numero: rlive.phase === 'mise' ? null : rlive.numero, historique: rlive.historique,
        gagnants: rlive.phase === 'resultat' ? rlive.gagnants : [], nbGagnants: rlive.phase === 'resultat' ? rlive.nbGagnants : 0, totalGagne: rlive.phase === 'resultat' ? rlive.totalGagne : 0,
        mises: r ? r.mises : {}, gain: prec ? prec.gain : 0, derniere: compte.rliveDerniere || {}, solde: compte.solde });
    }
    if (route === '/api/rlive-miser' && req.method === 'POST') {
      if (rlive.phase !== 'mise' || Date.now() > rlive.echeance - 150) return repondre(res, 409, { erreur: 'Les jeux sont faits, attendez le prochain tour.' });
      const voulu = body && typeof body.mises === 'object' && body.mises ? body.mises : {};
      const propre = {}; let total = 0;
      for (const k of Object.keys(voulu)) {
        const v = sous(Number(voulu[k]) || 0); if (v <= 0) continue;
        if (!rlCase(k)) return repondre(res, 400, { erreur: 'Mise invalide.' });
        if (v < 0.10) return repondre(res, 400, { erreur: 'Jeton minimum : 0,10 €.' });
        if (v > 250000) return repondre(res, 400, { erreur: 'Maximum 250 000 € par case.' });
        propre[k] = v; total += v;
      }
      total = sous(total);
      if (total > 250000) return repondre(res, 400, { erreur: 'Maximum 250 000 € par tour.' });
      const avant = compte.rlive && compte.rlive.tour === rlive.tour ? compte.rlive : { tour: rlive.tour, mises: {} };
      let deja = 0; Object.keys(avant.mises).forEach(k => { deja += avant.mises[k]; });
      const diff = sous(total - deja);
      if (diff > compte.solde + 1e-9) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      compte.solde = sous(compte.solde - diff);
      compte.rlive = { tour: rlive.tour, mises: propre };
      if (total > 0) compte.rliveDerniere = propre;
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, mises: propre, solde: compte.solde });
    }

    if (route === '/api/mines-demarrer' && req.method === 'POST') {
      if (compte.mines) return repondre(res, 409, { erreur: 'Une partie est deja en cours.' });
      const mise = sous(Number(body.mise) || 0);
      const nb = Number(body.mines) | 0;
      if (!(nb >= 1 && nb <= 24)) return repondre(res, 400, { erreur: 'Choisissez entre 1 et 24 mines.' });
      if (!(mise >= 0.10)) return repondre(res, 400, { erreur: 'Mise minimum : 0,10 €.' });
      if (mise > 1000)     return repondre(res, 400, { erreur: 'Mise maximum : 1 000 €.' });
      if (mise > compte.solde) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      const cases = []; for (let i = 0; i < 25; i++) cases.push(i);
      for (let i = 24; i > 0; i--) { const j = crypto.randomInt(i + 1); const t = cases[i]; cases[i] = cases[j]; cases[j] = t; }
      compte.solde = sous(compte.solde - mise);
      compte.mines = { mise: mise, nb: nb, mines: cases.slice(0, nb), ouverts: [] };
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, mise: mise, mines: nb, suivant: pouletMult(nb, 1), solde: compte.solde });
    }
    if (route === '/api/mines-ouvrir' && req.method === 'POST') {
      const p = compte.mines;
      if (!p) return repondre(res, 409, { erreur: 'Aucune partie en cours.' });
      const c = Number(body.case);
      if (!(Number.isInteger(c) && c >= 0 && c < 25)) return repondre(res, 400, { erreur: 'Case inconnue.' });
      if (p.ouverts.includes(c)) return repondre(res, 400, { erreur: 'Case deja ouverte.' });
      if (p.mines.includes(c)) {
        compte.mines = null;
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, mine: true, case: c, toutes: p.mines, perdu: p.mise, solde: compte.solde });
      }
      p.ouverts.push(c);
      const k = p.ouverts.length;
      const mult = pouletMult(p.nb, k);
      const gain = Math.min(30000, sous(p.mise * mult));
      if (k >= 25 - p.nb || gain >= 30000) {
        compte.solde = sous(compte.solde + gain);
        compte.mines = null;
        soldeAuSiege(compte);
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, mine: false, case: c, mult: mult, gain: gain, fini: true, toutes: p.mines, solde: compte.solde });
      }
      return repondre(res, 200, { ok: true, mine: false, case: c, mult: mult, gain: gain, suivant: pouletMult(p.nb, k + 1), solde: compte.solde });
    }
    if (route === '/api/mines-encaisser' && req.method === 'POST') {
      const p = compte.mines;
      if (!p) return repondre(res, 409, { erreur: 'Aucune partie en cours.' });
      if (!p.ouverts.length) return repondre(res, 400, { erreur: 'Ouvrez au moins une case avant d\'encaisser.' });
      const mult = pouletMult(p.nb, p.ouverts.length);
      const gain = Math.min(30000, sous(p.mise * mult));
      compte.solde = sous(compte.solde + gain);
      compte.mines = null;
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, gain: gain, mult: mult, toutes: p.mines, solde: compte.solde });
    }
    if (route === '/api/mines-etat' && req.method === 'POST') {
      const p = compte.mines;
      if (!p) return repondre(res, 200, { ok: true, enCours: false, solde: compte.solde });
      return repondre(res, 200, { ok: true, enCours: true, mise: p.mise, mines: p.nb, ouverts: p.ouverts,
        mult: p.ouverts.length ? pouletMult(p.nb, p.ouverts.length) : 0, suivant: pouletMult(p.nb, p.ouverts.length + 1), solde: compte.solde });
    }

    // une partie restee ouverte (page fermee) : on la reprend telle quelle
    if (route === '/api/poulet-etat' && req.method === 'POST') {
      const p = compte.poulet;
      if (!p) return repondre(res, 200, { ok: true, enCours: false, solde: compte.solde });
      return repondre(res, 200, { ok: true, enCours: true, mise: p.mise, os: p.nbOs, ouverts: p.ouverts,
        mult: p.ouverts.length ? pouletMult(p.nbOs, p.ouverts.length) : 0, solde: compte.solde });
    }

    /* ===============================================================
       THIMBLES (les gobelets)
       ---------------------------------------------------------------
       La mise part au depart. Le resultat est tire ICI au moment du
       choix du gobelet : 1 chance sur 3 avec 1 bille (x2,97), 2 sur 3
       avec 2 billes (x1,48). Gain plafonne a mise + 10 000 EUR.
       =============================================================== */
    /* ===============================================================
       SLOT GAMES : une mise = un tour complet (avec les tours gratuits).
       Tout est tire ICI ; la page ne fait qu'animer le resultat.
       =============================================================== */


    // ---------- LIVE BLACKJACK ----------
    if (route.startsWith('/api/lbj-')) { lbjRoutes(route, compte, body, res, req); if (res.headersSent) return; }
    /* LIVE BLACKJACK ETHAN : meme moteur, mais sa propre main et son propre sabot */
    if (route.startsWith('/api/lbt-')) { lbtRoutes(route, compte, body, res); return; }
    if (route === '/api/croupier-erreur' && req.method === 'POST') {
      CROUPIER_ERREUR_TEL = { quand: new Date().toISOString(), joueur: compte.pseudo, etape: String(body.etape || '').slice(0, 80), detail: String(body.detail || '').slice(0, 400), appareil: String(req.headers['user-agent'] || '').slice(0, 160) };
      console.log('[ETHAN] erreur telephone', JSON.stringify(CROUPIER_ERREUR_TEL));
      return repondre(res, 200, { ok: true });
    }
    /* ETHAN (LiveAvatar, mode FULL) : la cle secrete reste ICI, jamais dans la page.
       1) POST /v1/sessions/token  (en-tete X-API-KEY)   -> session_token
       2) POST /v1/sessions/start  (Bearer session_token) -> salle LiveKit
       La page ne recoit que l'adresse de la salle et son jeton d'entree. */
    if (route === '/api/ethan-session' && req.method === 'POST') {
      const nettoie = v => String(v || '').trim().replace(/^["']|["']$/g, '');
      const CLE = nettoie(process.env.LIVEAVATAR_API_KEY), AVATAR = nettoie(process.env.LIVEAVATAR_AVATAR_ID), AGENT = nettoie(process.env.LIVEAVATAR_VOICE_AGENT_ID);
      /* schema documente (Voice Agents) : { mode:'FULL', avatar_id, voice_agent:{ id } } — avatar_persona n'est jamais envoye */
      if (CLE && AVATAR && !AGENT) { CROUPIER_ERREUR = { quand: new Date().toISOString(), etape: 'variables Render', detail: 'LIVEAVATAR_VOICE_AGENT_ID vide ou absente : le serveur ne la recoit pas.' }; return repondre(res, 503, { erreur: 'LIVEAVATAR_VOICE_AGENT_ID vide ou absente sur le serveur' }); }
      if (!CLE || !AVATAR) { CROUPIER_ERREUR = { quand: new Date().toISOString(), etape: 'variables Render', detail: (!CLE ? 'LIVEAVATAR_API_KEY manquante. ' : '') + (!AVATAR ? 'LIVEAVATAR_AVATAR_ID manquante.' : '') }; return repondre(res, 503, { erreur: 'configuration serveur incomplete (' + CROUPIER_ERREUR.detail.trim() + ')' }); }
      const maintenant = Date.now();
      if (compte.ethanDernier && maintenant - compte.ethanDernier < 8000) return repondre(res, 429, { erreur: 'Patientez quelques secondes.' });
      compte.ethanDernier = maintenant;
      const BASE = 'https://api.liveavatar.com';
      const demande = croupierDemande();
      try {
        const r1 = await fetch(BASE + '/v1/sessions/token', { method: 'POST', headers: { 'X-API-KEY': CLE, 'Content-Type': 'application/json', 'Accept': 'application/json' }, body: JSON.stringify(demande) });
        const j1 = await r1.json().catch(() => ({}));
        const jeton = j1 && j1.data && j1.data.session_token;
        if (!r1.ok || !jeton) { console.log('[ETHAN] token refuse', r1.status, JSON.stringify(j1).slice(0, 400)); CROUPIER_ERREUR = { quand: new Date().toISOString(), etape: 'POST https://api.liveavatar.com/v1/sessions/token', requete_envoyee: demande, status_http: r1.status, reponse_liveavatar: croupierMasquer(j1) }; return repondre(res, 502, { erreur: 'LiveAvatar a refuse le token (HTTP ' + r1.status + ')', detail: croupierMasquer(j1) }); }
        const r2 = await fetch(BASE + '/v1/sessions/start', { method: 'POST', headers: { 'Authorization': 'Bearer ' + jeton, 'Accept': 'application/json' } });
        const j2 = await r2.json().catch(() => ({}));
        const d = (j2 && j2.data) || {};
        if (!r2.ok || !d.livekit_url || !d.livekit_client_token) { console.log('[ETHAN] start refuse', r2.status, JSON.stringify(j2).slice(0, 400)); CROUPIER_ERREUR = { quand: new Date().toISOString(), etape: 'POST https://api.liveavatar.com/v1/sessions/start', status_http: r2.status, reponse_liveavatar: croupierMasquer(j2) }; return repondre(res, 502, { erreur: 'LiveAvatar a refuse le demarrage (HTTP ' + r2.status + ')', detail: croupierMasquer(j2) }); }
        CROUPIER_OK = { quand: new Date().toISOString(), session_id: d.session_id };
        return repondre(res, 200, { ok: true, session_id: d.session_id, livekit_url: d.livekit_url, livekit_client_token: d.livekit_client_token, max_session_duration: d.max_session_duration || null });
      } catch (e) {
        console.log('[ETHAN] erreur', e && e.message); CROUPIER_ERREUR = { quand: new Date().toISOString(), etape: 'appel api.liveavatar.com', detail: String(e && e.message) };
        return repondre(res, 502, { erreur: 'LiveAvatar injoignable.' });
      }
    }
    if (route.startsWith('/api/lbe-')) {
      const m = compte.lbj, s = compte.lbjSabot;
      compte.lbj = compte.lbe || null; compte.lbjSabot = compte.lbeSabot; compte.__lbe = true;
      try { lbjRoutes(route.replace('/api/lbe-', '/api/lbj-'), compte, body, res, req); }
      finally { compte.lbe = compte.lbj; compte.lbeSabot = compte.lbjSabot; compte.lbj = m; compte.lbjSabot = s; compte.__lbe = false; }
      if (res.headersSent) return;
    }
    // ---------- CRASH GAME ----------
    if (route === '/api/avion-etat') return repondre(res, 200, avEtat(compte));
    if (route === '/api/avion-miser' && req.method === 'POST') {
      const slot = Number(body.slot) === 1 ? 1 : 0;
      const mise = sous(Number(body.mise) || 0);
      let auto = Number(body.auto) || 0; auto = auto >= 1.01 ? Math.min(AV_XMAX, Math.floor(auto * 100) / 100) : 0;
      if (!(mise >= AV_MIN && mise <= AV_MAX)) return repondre(res, 400, { erreur: 'Mise entre 0,10 € et 150 €.' });
      if (AVION.phase === 'attente' && AVION.paris.find(b => b.compte === compte && b.slot === slot)) return repondre(res, 409, { erreur: 'Pari deja place.' });
      if (mise > compte.solde + 1e-9) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      if (AVION.file.find(b => b.compte === compte && b.slot === slot)) return repondre(res, 409, { erreur: 'Pari deja place.' });
      compte.solde = sous(compte.solde - mise);
      const b = { compte, slot, mise, auto, actif: false, encaisse: false, x: 0, gain: 0 };
      if (AVION.phase === 'attente') AVION.paris.push(b); else AVION.file.push(b);
      soldeAuSiege(compte); Carnet.enregistrer(compte);
      return repondre(res, 200, avEtat(compte));
    }
    if (route === '/api/avion-annuler' && req.method === 'POST') {
      const slot = Number(body.slot) === 1 ? 1 : 0;
      let i = AVION.file.findIndex(b => b.compte === compte && b.slot === slot), liste = AVION.file;
      if (i < 0 && AVION.phase === 'attente') { liste = AVION.paris; i = liste.findIndex(b => b.compte === compte && b.slot === slot); }
      if (i < 0) return repondre(res, 409, { erreur: 'Trop tard pour annuler.' });
      const b = liste.splice(i, 1)[0];
      compte.solde = sous(compte.solde + b.mise);
      compte.points = Math.max(0, (compte.points | 0) - Math.round(b.mise * 100));
      if (res.__suivi) res.__suivi.deja = true;
      soldeAuSiege(compte); Carnet.enregistrer(compte);
      return repondre(res, 200, avEtat(compte));
    }
    if (route === '/api/avion-auto' && req.method === 'POST') {
      const b = avTrouver(compte, Number(body.slot) === 1 ? 1 : 0);
      let auto = Number(body.auto) || 0; auto = auto >= 1.01 ? Math.min(AV_XMAX, Math.floor(auto * 100) / 100) : 0;
      if (b && !b.encaisse) b.auto = auto;
      return repondre(res, 200, avEtat(compte));
    }
    if (route === '/api/avion-encaisser' && req.method === 'POST') {
      const slot = Number(body.slot) === 1 ? 1 : 0;
      const b = AVION.paris.find(x => x.compte === compte && x.slot === slot);
      if (AVION.phase === 'vol' && b && b.actif && !b.encaisse) {
        const el = Date.now() - AVION.debut;
        if (avBrut(el) < AVION.crash) {
          const gain = avCrediter(b, avMult(el), false);
          if (res.__suivi) res.__suivi.deja = true;
          const e = avEtat(compte); e.gain = gain; e.x = b.x;
          return repondre(res, 200, e);
        }
      }
      return repondre(res, 409, Object.assign(avEtat(compte), { ok: false, erreur: 'Trop tard !' }));
    }

    if (route === '/api/slot-jouer' && req.method === 'POST') {
      const id = String(body.jeu || '');
      if (!SLOTS_OUVERTS.includes(id)) return repondre(res, 400, { erreur: 'Jeu inconnu.' });
      const mise = sous(Number(body.mise) || 0);
      if (!(mise >= 0.2 && mise <= 500)) return repondre(res, 400, { erreur: 'Mise entre 0,20 € et 500 €.' });
      if (mise > compte.solde) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      const alea = () => crypto.randomInt(0, 1000000000) / 1000000000;
      let tirage;
      if (id === 'volcan') { tirage = jouerVolcan(VOLCAN, alea); tirage.total = Math.min(SLOTS.GAIN_MAX, tirage.total); }
      else tirage = SLOTS.jouer(id, alea);
      const gain = sous(tirage.total * mise);
      compte.solde = sous(compte.solde - mise + gain);
      if (res.__suivi) res.__suivi.nomJeu = NOMS_SLOTS[id];
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, res: tirage, gain, solde: compte.solde });
    }

    if (route === '/api/thimbles-demarrer' && req.method === 'POST') {
      if (compte.thimbles) return repondre(res, 409, { erreur: 'Une partie est deja en cours.' });
      const mise = sous(Number(body.mise) || 0), billes = Number(body.billes) === 2 ? 2 : 1;
      if (!(mise >= 0.20)) return repondre(res, 400, { erreur: 'Mise minimum : 0,20 €.' });
      if (mise > 1000)     return repondre(res, 400, { erreur: 'Mise maximum : 1 000 €.' });
      if (mise > compte.solde) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      compte.solde = sous(compte.solde - mise);
      compte.thimbles = { mise, billes };
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, mise, billes, solde: compte.solde });
    }
    if (route === '/api/thimbles-choisir' && req.method === 'POST') {
      const t = compte.thimbles;
      if (!t) return repondre(res, 409, { erreur: 'Aucune partie en cours.' });
      compte.thimbles = null;
      const mult = t.billes === 2 ? 1.48 : 2.97;
      const gagne = crypto.randomInt(3) < t.billes;
      const gain = gagne ? Math.min(sous(t.mise * mult), sous(t.mise + 10000)) : 0;
      if (gain) { compte.solde = sous(compte.solde + gain); soldeAuSiege(compte); }
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, gagne, mult, gain, mise: t.mise, solde: compte.solde });
    }
    if (route === '/api/thimbles-etat' && req.method === 'POST') {
      const t = compte.thimbles;
      return repondre(res, 200, t ? { ok: true, enCours: true, mise: t.mise, billes: t.billes, solde: compte.solde } : { ok: true, enCours: false, solde: compte.solde });
    }

    /* ===============================================================
       LE PLINKO
       ---------------------------------------------------------------
       Chaque balle : une suite de gauche/droite tiree ICI (une par
       rangee). La case d'arrivee = nombre de "droite". La mise est
       partagee entre les balles. Tout est paye tout de suite ; la page
       ne fait que rejouer les chemins. Gain plafonne a mise + 10 000 EUR.
       =============================================================== */
    if (route === '/api/plinko-lancer' && req.method === 'POST') {
      const mise = sous(Number(body.mise) || 0);
      const n = Number(body.rangees) | 0, nbBalles = Number(body.balles) | 0;
      const table = PLINKO_TABLES[body.risque] && PLINKO_TABLES[body.risque][n];
      if (!table) return repondre(res, 400, { erreur: 'Reglage inconnu.' });
      if (!(nbBalles >= 1 && nbBalles <= 20)) return repondre(res, 400, { erreur: 'De 1 a 20 balles.' });
      if (!(mise >= 0.20)) return repondre(res, 400, { erreur: 'Mise minimum : 0,20 €.' });
      if (mise > 1000)     return repondre(res, 400, { erreur: 'Mise maximum : 1 000 €.' });
      if (mise > compte.solde) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      const parBalle = mise / nbBalles, chemins = [], gains = [], mults = [];
      let total = 0;
      for (let b = 0; b < nbBalles; b++) {
        let ch = '', k = 0;
        for (let r = 0; r < n; r++) { const d = crypto.randomInt(2); ch += d; k += d; }
        const m = table[k], g = sous(parBalle * m);
        chemins.push(ch); mults.push(m); gains.push(g); total += g;
      }
      total = Math.min(sous(total), sous(mise + 10000));
      compte.solde = sous(compte.solde - mise + total);
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, chemins, gains, mults, total, solde: compte.solde });
    }

    /* ===============================================================
       LE KOALA ROAD
       ---------------------------------------------------------------
       A chaque voie, une chance de croiser une voiture est tiree ICI,
       au moment ou le joueur avance (jamais a l'avance) : les voitures
       peuvent vraiment debarquer n'importe quand, rien n'est ecrit
       d'avance sur le trajet. =============================================================== */
    if (route === '/api/kroad-demarrer' && req.method === 'POST') {
      if (compte.kroad) return repondre(res, 409, { erreur: 'Une traversee est deja en cours.' });
      const mise = sous(Number(body.mise) || 0);
      const risque = body.risque;
      if (!KROAD_RISQUES[risque]) return repondre(res, 400, { erreur: 'Niveau de risque inconnu.' });
      if (!(mise >= 0.20)) return repondre(res, 400, { erreur: 'Mise minimum : 0,20 €.' });
      if (mise > 1000)     return repondre(res, 400, { erreur: 'Mise maximum : 1 000 €.' });
      if (mise > compte.solde) return repondre(res, 400, { erreur: 'Solde insuffisant.' });
      compte.solde = sous(compte.solde - mise);
      compte.kroad = { mise, risque, voie: 0 };
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, mise, risque, solde: compte.solde });
    }

    if (route === '/api/kroad-avancer' && req.method === 'POST') {
      const k = compte.kroad;
      if (!k) return repondre(res, 409, { erreur: 'Aucune traversee en cours.' });
      const p = KROAD_RISQUES[k.risque];
      const heurte = crypto.randomInt(1000000) < Math.round(p * 1000000);
      if (heurte) {
        compte.kroad = null;
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, heurte: true, voie: k.voie + 1, perdu: k.mise, solde: compte.solde });
      }
      k.voie++;
      compte.kroadVoies = (compte.kroadVoies | 0) + 1;
      const mult = kroadMult(k.risque, k.voie);
      const gain = Math.min(10000, sous(k.mise * mult));
      if (k.voie >= KROAD_VOIES_MAX || gain >= 10000) {      // trop loin ou plafond : on encaisse d'office
        compte.solde = sous(compte.solde + gain);
        compte.kroad = null;
        soldeAuSiege(compte);
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, heurte: false, voie: k.voie, mult, gain, fini: true, solde: compte.solde });
      }
      return repondre(res, 200, { ok: true, heurte: false, voie: k.voie, mult, gain, suivant: kroadMult(k.risque, k.voie + 1), solde: compte.solde });
    }

    if (route === '/api/kroad-encaisser' && req.method === 'POST') {
      const k = compte.kroad;
      if (!k) return repondre(res, 409, { erreur: 'Aucune traversee en cours.' });
      if (k.voie < 1) return repondre(res, 400, { erreur: 'Avancez au moins une voie avant d\'encaisser.' });
      const mult = kroadMult(k.risque, k.voie);
      const gain = Math.min(10000, sous(k.mise * mult));
      compte.solde = sous(compte.solde + gain);
      compte.kroad = null;
      soldeAuSiege(compte);
      Carnet.enregistrer(compte);
      return repondre(res, 200, { ok: true, gain, mult, voie: k.voie, solde: compte.solde });
    }

    if (route === '/api/kroad-etat' && req.method === 'POST') {
      const k = compte.kroad;
      if (!k) return repondre(res, 200, { ok: true, enCours: false, solde: compte.solde });
      return repondre(res, 200, { ok: true, enCours: true, mise: k.mise, risque: k.risque, voie: k.voie,
        mult: k.voie ? kroadMult(k.risque, k.voie) : 0, solde: compte.solde });
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
      if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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

      // le sommet (niveau TOWER_NIVEAUX, plafond TOWER_MULT_MAX, ou 30 000 EUR atteints) : on encaisse d\'office
      if (r.sommet || tour.mise * tour.totalMult >= TOWER_GAIN_MAX) {
        const gain = Math.min(TOWER_GAIN_MAX, sous(tour.mise * tour.totalMult));
        compte.solde = sous(compte.solde + gain);
        compte.tower = null;
        const info = siegeDe(compte);
        if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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

      const gain = Math.min(TOWER_GAIN_MAX, sous(tour.mise * Math.min(TOWER_MULT_MAX, tour.totalMult)));
      compte.solde = sous(compte.solde + gain);
      compte.tower = null;

      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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
        if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
        Carnet.enregistrer(compte);
        return repondre(res, 200, { ok: true, genre: 'credit', solde: compte.solde });
      }

      // Codes reserves au proprietaire du site. Change-les si tu penses que
      // quelqu\'un d\'autre les connait : c\'est la seule protection, donc ils
      // ne doivent JAMAIS apparaitre dans index.html, ni dans un fichier
      // partage avec quelqu\'un d\'autre, ni etre dits a voix haute.
      if (normalise === 'kq8') {                     // les gros gains de l'accueil, pour pouvoir en effacer
        return repondre(res, 200, { ok: true, genre: 'gains', gains: GROS_GAINS.slice(0, 10) });
      }
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
        if (c.pseudoBas === cibleSol) { c.soldeHorsNom = 'Ajustement admin'; c.solde = nouveauSolde; }
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
        const info = siegeDe(compte); if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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
        const info = siegeDe(compte); if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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
        const info = siegeDe(compte); if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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
        const info = siegeDe(compte); if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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
        const info = siegeDe(compte); if (info && info.p) { info.p.solde = compte.solde; info.p.soldeRef = compte.solde; touche(info.table); }
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
        points:   compte.points | 0,
        kroadVoies: compte.kroadVoies | 0,
        blockBest: compte.blockBest | 0,
        blockVides: compte.blockVides | 0,
        tx:       (compte.tx || []).slice(0, 60),
        voiturePremium: !!compte.voiturePremium,
        voitureHybride: !!compte.voitureHybride,
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
  /* seule la page du jeu est visible : tous les autres fichiers sont prives */
  if (route !== '/' && route !== '/index.html') { res.writeHead(404); res.end('Introuvable'); return; }
  let fichier = '/index.html';
  fichier = path.normalize(fichier).replace(/^(\.\.[\/\\])+/, '');

  // les fichiers de travail ne sont pas visibles depuis le site
  const nom = path.basename(fichier).toLowerCase();
  const PRIVES = ['serveur.js', 'package.json', 'package-lock.json', 'lisez-moi.txt'];
  if (PRIVES.indexOf(nom) >= 0 || nom.charAt(0) === '.') {
    res.writeHead(404); res.end('Introuvable'); return;
  }

  const chemin = path.join(DOSSIER, fichier);
  if (!chemin.startsWith(DOSSIER)) { res.writeHead(403); res.end('Interdit'); return; }
  servirFichier(res, chemin, req);
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
    voitureHybride: !!fiche.voitureHybride,
    codesUtilises: Array.isArray(fiche.codesUtilises) ? fiche.codesUtilises.slice() : [],
    points:    fiche.points | 0,
    kroadVoies: fiche.kroadVoies | 0,
    tx:        Array.isArray(fiche.tx) ? fiche.tx.slice(0, 60) : [],
    pecheJour: fiche.pecheJour || null,
    pecheAuj:  fiche.pecheAuj | 0,
    blockJour: fiche.blockJour || null,
    blockAuj:  fiche.blockAuj | 0,
    blockBest: fiche.blockBest | 0,
    blockVides: fiche.blockVides | 0,
    soldeSuivi: sous(Number(fiche.solde)),
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
    voitureHybride: !!compte.voitureHybride,
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
