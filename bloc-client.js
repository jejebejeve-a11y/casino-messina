/* ===================================================================
   5. BLACKJACK — les cartes sont tenues par le serveur
   -------------------------------------------------------------------
   Le jeu ne decide plus rien tout seul : il demande l'etat de la table
   au serveur, puis il anime ce qu'il recoit. Si le serveur ne repond
   pas, on reessaie simplement au tour suivant : rien ne se bloque.
   =================================================================== */

let JETON = null;

async function envoyer(route, donnees) {
  try {
    const r = await fetch('/api/' + route, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(Object.assign({ jeton: JETON }, donnees || {}))
    });
    return await r.json();
  } catch (e) { return { erreur: 'reseau' }; }
}

async function demander(route) {
  try {
    const r = await fetch('/api/' + route + '?jeton=' + encodeURIComponent(JETON || ''));
    return await r.json();
  } catch (e) { return { erreur: 'reseau' }; }
}

/* --- le solde suit le joueur dans son navigateur --- */
function chargerSolde() {
  try {
    const v = parseFloat(localStorage.getItem('messina_solde'));
    return (isFinite(v) && v >= 0) ? v : 22;
  } catch (e) { return 22; }
}
function sauverSolde() {
  try {
    if (E.joueur) localStorage.setItem('messina_solde', String(E.joueur.solde));
  } catch (e) {}
}

/* --- comptage, uniquement pour l'affichage --- */
function valeurCarte(c) {
  if (c.h === 'A') return 11;
  if (c.h === 'V' || c.h === 'D' || c.h === 'R') return 10;
  return parseInt(c.h, 10);
}
function compter(main) {
  let total = 0, as = 0;
  for (const c of main) { if (!c) continue; total += valeurCarte(c); if (c.h === 'A') as++; }
  while (total > 21 && as > 0) { total -= 10; as--; }
  return total;
}

/* --- ce qui est actuellement affiche a l'ecran --- */
const M = {
  banque: [], places: [null, null, null],
  indexActif: -1, phase: 'mise', cacheeRevelee: false
};

let sondage       = null;
let etatCible     = null;
let enAnimation   = false;
let dernierMot    = '';
let dernierResultat = '';

/* ===================================================================
   ARRIVEE ET DEPART
   =================================================================== */
async function rejoindreTable(id) {
  const e = await envoyer('asseoir', { table: id });
  if (!e || e.erreur) {
    direKoala(e && e.erreur === 'table complete'
      ? 'Cette table est pleine. Essayez l’autre.'
      : 'Le salon ne répond pas. Réessayez.');
    return;
  }

  E.table = { id: id, nom: e.nom };
  $('titreSalle').textContent = e.nom;
  montrerEcran('ecranSalle');
  initSon(); ambianceOn();

  M.banque = []; M.places = [null, null, null];
  M.cacheeRevelee = false; M.indexActif = -1; M.phase = e.phase;
  dessinerBanque(); dessinerPlaces();
  $('zoneResultat').textContent = '';
  $('zoneResultat').className = 'resultat serif';
  $('champMise').value = '';
  dernierMot = ''; dernierResultat = '';

  etatCible = e;
  synchroniser();
  demarrerSondage();
}

function quitterSalle() {
  arreterSondage();
  ambianceOff();
  E.table   = null;
  etatCible = null;
  montrerEcran('ecranApp');
  construireSalon();
  majSolde();
}

$('btnQuitter').onclick = async () => {
  arreterSondage();
  const t = E.table;
  E.table = null;
  quitterSalle();
  if (t) await envoyer('quitter', {});
};

/* ===================================================================
   ON DEMANDE L'ETAT AU SERVEUR, EN BOUCLE
   =================================================================== */
function demarrerSondage() {
  arreterSondage();
  sondage = setInterval(async () => {
    if (!E.table) return;
    const e = await demander('etat');
    if (!e || e.erreur) return;              // pas de reponse : on retentera
    if (e.assis === false) { quitterSalle(); return; }
    etatCible = e;
    synchroniser();
  }, 700);
}
function arreterSondage() {
  if (sondage) clearInterval(sondage);
  sondage = null;
}

async function synchroniser() {
  if (enAnimation) return;                    // une animation est deja en cours
  enAnimation = true;
  try {
    while (etatCible) {
      const e = etatCible;
      etatCible = null;
      await appliquer(e);
    }
  } catch (err) {
    // quoi qu'il arrive on ne reste jamais coince
  } finally {
    enAnimation = false;
  }
}

/* ===================================================================
   ON AFFICHE CE QUE LE SERVEUR NOUS A DIT
   =================================================================== */
async function appliquer(e) {
  if (!E.table || !e || !e.places) return;

  /* --- le solde --- */
  if (E.joueur && typeof e.monSolde === 'number') {
    E.joueur.solde = e.monSolde;
    majSolde();
    sauverSolde();
  }

  /* --- nouvelle manche : la table se vide d'un coup --- */
  const cartesServeur = e.banque.length +
    e.places.reduce((n, p) => n + (p ? p.main.length : 0), 0);
  const cartesEcran = M.banque.length +
    M.places.reduce((n, p) => n + (p ? p.main.length : 0), 0);

  if (cartesServeur === 0 && cartesEcran > 0) {
    M.banque = [];
    M.places = [null, null, null];
    M.cacheeRevelee = false;
    M.indexActif = -1;
    $('zoneResultat').textContent = '';
    $('zoneResultat').className = 'resultat serif';
    $('champMise').value = '';
    dernierResultat = '';
    dessinerBanque(); dessinerPlaces();
  }

  /* --- qui est assis --- */
  for (let i = 0; i < 3; i++) {
    const s = e.places[i];
    if (!s) { M.places[i] = null; continue; }
    if (!M.places[i] || M.places[i].nom !== s.nom) {
      M.places[i] = { nom: s.nom, moi: s.moi, bot: s.bot, mise: s.mise, main: [], etat: s.etat };
    } else {
      M.places[i].mise = s.mise;
      M.places[i].etat = s.etat;
      M.places[i].moi  = s.moi;
    }
  }

  /* --- les cartes qui viennent d'arriver, une par une --- */
  let securite = 0;
  while (securite++ < 24) {
    let posee = false;

    for (let i = 0; i < 3; i++) {
      const s = e.places[i], d = M.places[i];
      if (s && d && d.main.length < s.main.length) {
        await volerCarte();
        if (!E.table) return;
        d.main.push(s.main[d.main.length]);
        dessinerPlaces();
        posee = true;
        break;
      }
    }
    if (posee) continue;

    if (M.banque.length < e.banque.length) {
      await volerCarte();
      if (!E.table) return;
      M.banque.push(e.banque[M.banque.length]);
      dessinerBanque();
      continue;
    }
    break;
  }

  /* --- la carte cachee se retourne --- */
  if (e.cacheeRevelee && !M.cacheeRevelee) {
    M.banque = e.banque.slice(0, M.banque.length);
    M.cacheeRevelee = true;
    dessinerBanque();
    await attendre(420);
    if (!E.table) return;
  }

  /* --- de qui est-ce le tour --- */
  M.indexActif = e.indexActif;
  M.phase      = e.phase;
  dessinerPlaces();

  /* --- la parole du croupier --- */
  if (e.message && e.message !== dernierMot) {
    dernierMot = e.message;
    direKoala(e.message);
  }

  /* --- plus un centime --- */
  if (e.monSolde < 0.01 && (e.phase === 'mise' || e.phase === 'attente')) {
    $('libellePhase').innerHTML = '<b>Plus un centime.</b> Allez pêcher avec Jeffrey.';
    $('zoneMise').style.display   = 'none';
    $('zoneActions').style.display = 'none';
    majBarre(0, 10);
    setTimeout(() => { if (E.table) $('btnQuitter').onclick(); }, 3500);
    return;
  }

  /* --- les boutons et le chronometre --- */
  majCommandes(e);

  /* --- le resultat de la manche --- */
  if (e.monResultat && e.monResultat.texte !== dernierResultat) {
    dernierResultat = e.monResultat.texte;
    $('zoneResultat').textContent = e.monResultat.texte;
    $('zoneResultat').className   = 'resultat serif ' + (e.monResultat.classe || '');
    if (e.monResultat.classe === 'gagne')      sonGain();
    else if (e.monResultat.classe === 'perdu') sonPerte();
    E.mains++;
  }

  /* --- Don Koala se paie la tete du perdant, chez lui seulement --- */
  if (e.provocation) {
    await provoquerPerdant();
  }
}

function majCommandes(e) {
  const zMise = $('zoneMise'), zAct = $('zoneActions'), lib = $('libellePhase');

  if (e.phase === 'mise') {
    const aMise = e.maMise > 0;
    zMise.style.display = aMise ? 'none' : 'block';
    zAct.style.display  = 'none';
    lib.innerHTML = aMise
      ? 'Mise posée — <b>' + eur(e.maMise) + '</b>. On attend les autres.'
      : 'Placez vos mises — <b>' + e.secondes + ' s</b>';
    majBarre(e.secondes, 10);
    return;
  }

  zMise.style.display = 'none';

  if (e.phase === 'joueur' && e.monTour) {
    zAct.style.display = 'flex';
    $('btnDoubler').disabled = !e.peutDoubler;
    lib.innerHTML = 'À vous — <b>' + e.secondes + ' s</b>';
    majBarre(e.secondes, 10);
    return;
  }

  zAct.style.display = 'none';

  if (e.phase === 'distribution')   lib.textContent = 'Don Koala distribue';
  else if (e.phase === 'banque')    lib.textContent = 'La banque joue';
  else if (e.phase === 'resultat')  lib.textContent = 'Manche suivante…';
  else if (e.phase === 'attente')   lib.textContent = 'En attente de joueurs…';
  else {
    const p = e.places[e.indexActif];
    lib.textContent = p ? p.nom + ' réfléchit…' : 'Un instant…';
  }
  majBarre(0, 10);
}

function majBarre(reste, total) {
  const b = $('barreChrono');
  if (!b) return;
  b.style.transition = 'transform .75s linear';
  b.style.transform  = 'scaleX(' + Math.max(0, Math.min(1, reste / total)) + ')';
}

/* ===================================================================
   LES MISES
   =================================================================== */
const JETONS = [0.01, 0.10, 0.50, 1, 2, 5, 10];
(function construireJetons() {
  const z = $('jetons');
  JETONS.forEach(v => {
    const d = document.createElement('div');
    d.className = 'jeton';
    d.textContent = eur(v);
    d.onclick = () => { $('champMise').value = v.toFixed(2); };
    z.appendChild(d);
  });
  const tout = document.createElement('div');
  tout.className = 'jeton';
  tout.textContent = 'Tapis';
  tout.onclick = () => { if (E.joueur) $('champMise').value = E.joueur.solde.toFixed(2); };
  z.appendChild(tout);
})();

$('btnMiser').onclick = async () => {
  if (M.phase !== 'mise') return;
  const v = parseFloat(String($('champMise').value).replace(',', '.'));
  if (!isFinite(v) || v < 0.01) { direKoala('Une mise, même d’un centime.'); return; }
  if (!E.joueur || v > E.joueur.solde + 1e-9) { direKoala('Votre solde ne suit pas.'); return; }

  $('zoneMise').style.display = 'none';
  sonJeton();

  const e = await envoyer('miser', { mise: Math.round(v * 100) / 100 });
  if (!e || e.erreur) {
    direKoala('Mise refusée.');
    if (M.phase === 'mise') $('zoneMise').style.display = 'block';
    return;
  }
  etatCible = e;
  synchroniser();
};

/* ===================================================================
   CARTE, RESTER, DOUBLER
   =================================================================== */
async function agir(action) {
  $('zoneActions').style.display = 'none';
  const e = await envoyer('action', { action: action });
  if (!e || e.erreur) return;
  etatCible = e;
  synchroniser();
}

$('btnCarte').onclick   = () => { if (M.phase === 'joueur') agir('carte');   };
$('btnRester').onclick  = () => { if (M.phase === 'joueur') agir('rester');  };
$('btnDoubler').onclick = () => { if (M.phase === 'joueur') agir('doubler'); };

/* ===================================================================
   ANIMATIONS ET RENDU  (inchanges)
   =================================================================== */

/* carte animée qui part de la patte du koala */
function volerCarte() {
  return new Promise(resolve => {
    const zone = $('zoneVol');
    const s = $('scene').getBoundingClientRect();
    if (!s.width) { resolve(); return; }

    const c = document.createElement('div');
    c.className = 'carte-vol';
    // la patte du croupier se trouve autour de 28 % / 78 % sur la photo
    const x0 = s.width * 0.28, y0 = s.height * 0.76;
    const x1 = s.width * (0.35 + Math.random() * 0.34);
    const y1 = s.height * 1.02;
    c.style.left = x0 + 'px';
    c.style.top  = y0 + 'px';
    c.style.transform = 'translate(-50%,-50%) rotate(-18deg) scale(.55)';
    c.style.opacity = '0';
    zone.appendChild(c);

    sonCarte();
    const lu = $('lueurPatte'), sc = $('scene');
    if (lu) { lu.classList.remove('sert'); void lu.offsetWidth; lu.classList.add('sert'); }
    if (sc) { sc.classList.remove('sert'); void sc.offsetWidth; sc.classList.add('sert'); }
    requestAnimationFrame(() => {
      c.style.transition = 'transform .52s cubic-bezier(.34,.62,.35,1), opacity .13s linear, left .52s cubic-bezier(.34,.62,.35,1), top .52s cubic-bezier(.34,.62,.35,1)';
      c.style.opacity = '1';
      c.style.left = x1 + 'px';
      c.style.top  = y1 + 'px';
      c.style.transform = 'translate(-50%,-50%) rotate(' + (Math.random() * 40 - 20) + 'deg) scale(1)';
    });

    setTimeout(() => { c.remove(); resolve(); }, 600);
  });
}

/* --- Don Koala se paie la tete du perdant --- */
async function provoquerPerdant() {
  const boite = $('provoc'), scene = $('scene');
  if (!boite || !scene) return;

  const piques = [
    'Deux fois de suite', 'La maison te remercie', 'Rentre chez toi',
    'Ramene du poisson', 'Tu joues ou tu donnes ?'
  ];
  const sous = $('provocSous');
  if (sous) sous.textContent = piques[Math.floor(Math.random() * piques.length)];

  // on relance les animations depuis zero
  boite.classList.remove('actif');
  scene.classList.remove('rigole');
  void boite.offsetWidth;
  boite.classList.add('actif');
  scene.classList.add('rigole');

  const b = $('bulleKoala');
  if (b) b.classList.remove('visible');

  sonRire();
  setTimeout(function () { voixKoala('Loser !'); }, 520);
  setTimeout(function () { sonRire(); }, 1500);

  await attendre(3400);
  boite.classList.remove('actif');
  scene.classList.remove('rigole');
}

/* --- rendu --- */
function carteHTML(c, cachee) {
  if (cachee || !c) return '<div class="pc dos"></div>';
  return '<div class="pc' + (c.r ? ' r' : '') + '">' +
           '<div class="h">' + c.h + '</div>' +
           '<div class="c">' + c.s + '</div>' +
           '<div class="b">' + c.h + '</div>' +
         '</div>';
}

function dessinerBanque() {
  const z = $('mainBanque');
  z.innerHTML = M.banque.map(c => carteHTML(c, !c)).join('');

  const s = $('scoreBanque');
  if (M.banque.length === 0) { s.textContent = '—'; s.className = 'score-bulle'; return; }

  if (M.banque.some(c => !c)) {
    s.textContent = compter([M.banque[0]]) + ' + ?';
    s.className = 'score-bulle';
  } else {
    const t = compter(M.banque);
    s.textContent = t > 21 ? t + ' — saute' : String(t);
    s.className = 'score-bulle' + (t > 21 ? ' saute' : '');
  }
}

function dessinerPlaces() {
  const z = $('siegesJeu');
  z.innerHTML = M.places.map((p, i) => {
    if (!p) return '<div class="place vide">Place libre</div>';
    const t = compter(p.main);
    const actif = i === M.indexActif && (M.phase === 'joueur' || M.phase === 'bot');
    return '<div class="place' + (p.moi ? ' moi' : '') + (actif ? ' tour' : '') + '">' +
             '<div class="place-nom">' + p.nom + (p.moi ? ' · vous' : '') + '</div>' +
             '<div class="place-mise">' + (p.mise > 0 ? eur(p.mise) : '—') + '</div>' +
             '<div class="main-cartes">' + p.main.map(c => carteHTML(c, false)).join('') + '</div>' +
             (p.main.length
               ? '<div class="score-bulle' + (t > 21 ? ' saute' : '') + '">' + (t > 21 ? t + ' ✕' : t) + '</div>'
               : '') +
           '</div>';
  }).join('');
}
