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
   COMPTES
   =================================================================== */
const comptes = new Map();   // jeton -> { pseudo, solde, table, siege, vu }

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

    // --- ouverture de session ---
    if (route === '/api/session' && req.method === 'POST') {
      const body = await corpsJSON(req);
      const pseudo = String(body.pseudo || '').trim().slice(0, 18) || 'Joueur';
      let solde = Number(body.solde);
      if (!isFinite(solde) || solde < 0 || solde > 100000) solde = SOLDE_DEPART;
      const jeton = nouveauJeton();
      comptes.set(jeton, {
        jetonRef: jeton, pseudo, solde: sous(solde),
        table: null, siege: -1, vu: Date.now()
      });
      return repondre(res, 200, { jeton, pseudo, solde: sous(solde) });
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

    // --- mise a jour du solde (retour de peche) ---
    if (route === '/api/solde' && req.method === 'POST') {
      let v = Number(body.solde);
      if (!isFinite(v) || v < 0 || v > 100000) return repondre(res, 400, { erreur: 'solde invalide' });
      compte.solde = sous(v);
      const info = siegeDe(compte);
      if (info && info.p) { info.p.solde = compte.solde; touche(info.table); }
      return repondre(res, 200, { solde: compte.solde });
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

serveur.listen(PORT, () => {
  console.log('Casino Messina — le salon est ouvert sur le port ' + PORT);
});
