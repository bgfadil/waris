/* Mesin hitung waris KHI (JS) v0.5: port dari waris_engine.py + waris_lanjut.py. Alat bantu, bukan fatwa. */
(function (root) {
'use strict';
const gcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };
class Fr {
  constructor(n, d = 1n) { n = BigInt(n); d = BigInt(d); if (d === 0n) throw new RangeError('bagi nol'); if (d < 0n) { n = -n; d = -d; } const g = gcd(n, d) || 1n; this.n = n / g; this.d = d / g; }
  static of(x) {
    if (x instanceof Fr) return x;
    if (typeof x === 'string') { const [a, b] = x.split('/'); return new Fr(a, b === undefined ? 1 : b); }
    if (typeof x === 'number' && !Number.isInteger(x)) return new Fr(Math.round(x * 1e9), 1e9);
    return new Fr(x);
  }
  add(o) { o = Fr.of(o); return new Fr(this.n * o.d + o.n * this.d, this.d * o.d); }
  sub(o) { o = Fr.of(o); return new Fr(this.n * o.d - o.n * this.d, this.d * o.d); }
  mul(o) { o = Fr.of(o); return new Fr(this.n * o.n, this.d * o.d); }
  div(o) { o = Fr.of(o); return new Fr(this.n * o.d, this.d * o.n); }
  cmp(o) { o = Fr.of(o); const x = this.n * o.d - o.n * this.d; return x < 0n ? -1 : x > 0n ? 1 : 0; }
  lt(o) { return this.cmp(o) < 0; } gt(o) { return this.cmp(o) > 0; } le(o) { return this.cmp(o) <= 0; } eq(o) { return this.cmp(o) === 0; }
  num() { return Number(this.n) / Number(this.d); }
  toString() { return this.d === 1n ? String(this.n) : this.n + '/' + this.d; }
}
const ZERO = new Fr(0), ONE = new Fr(1);
const sum = (a) => a.reduce((s, x) => s.add(x), ZERO);
const frs = (s) => (s == null ? null : Fr.of(s));
const INPUT = {anak_lk:[31,31],cucu_lk:[30,30],anak_pr:[28,29],cucu_pr:[26,27],suami:[25,25],ayah:[24,24],istri:[23,23],kakek:[22,22],
 sdr_lk_kandung:[20,21],sdri_kandung:[19,18],sdr_lk_seayah:[16,17],sdri_seayah:[15,14],sdr_lk_seibu:[11,13],sdri_seibu:[10,12],ibu:[9,9],
 nenek_ayah:[7,7],nenek_ibu:[8,8],kemenakan_kandung:[6,6],kemenakan_seayah:[5,5],paman_kandung:[4,4],paman_seayah:[3,3],sepupu_paman_kandung:[2,2],sepupu_paman_seayah:[1,1]};
const SEIBU = new Set([10,11,12,13]), KANDUNG_LK = new Set([20,21]), KANDUNG_PR = new Set([18,19]);
const LABEL = {'1/6A':'1/6A|1/6As','1/6As':'1/6A|1/6As',A:'A|As',As:'A|As','1/3':'1/3|1/2','1/2':'1/3|1/2','2/3':'2/3','<-S':'<-S|<-1/2','<-1/2':'<-S|<-1/2',
 '1/8':'1/8|Mj',Mj:'1/8|Mj','1/4':'1/4|1/6','1/6':'1/4|1/6','1/IV':'1/IV|1/VI','1/VI':'1/IV|1/VI',AI:'AI|AII',AII:'AI|AII'};
const TOK = {'Λ':'A','Λs':'As','1/6Λ':'1/6A','1/6Λs':'1/6As','←1/2':'<-1/2','←s':'<-S','←':'<-S','Λ1':'AI','Λ.j':'A','A.M':'A',
 '1/3a':'1/3','1/3b':'1/3','1/3c':'1/3','1/3d':'1/3','1/6M':'1/6','M+j':'Mj','1/3a+1/3b':'1/IV','1/3b+1/3c':'1/VI','1/3d+1/3d':'1/6'};
const eqSet = (s, arr) => s.size === arr.length && arr.every((x) => s.has(x));

class Waris {
  constructor(d) {
    this.d = d; this.G = new Map(d.jadwal.map((c) => [c.baris + ',' + c.kolom, c]));
    this.nomor = {}; d.nomor.forEach((n) => (this.nomor[n.no] = n));
    this.t7 = d.tabel_vii.baris;
  }
  pilih(c, present) {
    const cands = [];
    for (const r of [...present, 0]) {
      if (r !== 0 && r <= c) continue;
      const g = this.G.get(r + ',' + c); if (!g) throw new Error('sel tidak ada ' + r + ',' + c);
      const cell = { ...g, r }; if (cell.raw === '—') continue;
      if (cell.nilai_koreksi) { cell.nilai = cell.nilai_koreksi; cell.kelas = 10; }
      cands.push(cell);
    }
    const raws = cands.map((x) => x.raw);
    if (c === 9) {
      if (raws.filter((x) => x === '1/3d').length >= 2) cands.push({ raw: '1/3d+1/3d', tipe: 'furudh', kelas: 10, nilai: '1/6', marker: null, r: -1 });
      if (raws.includes('1/3a') && raws.includes('1/3b')) cands.push({ raw: '1/3a+1/3b', tipe: 'furudh', kelas: 15, nilai: '1/4', marker: null, r: -1 });
      if (raws.includes('1/3b') && raws.includes('1/3c')) cands.push({ raw: '1/3b+1/3c', tipe: 'furudh', kelas: 9, nilai: '1/6', marker: null, r: -1 });
    }
    const ms = new Set(cands.filter((x) => x.marker).map((x) => x.marker));
    if (ms.has('M') && ms.has('j')) cands.push({ raw: 'M+j', tipe: 'mahjub', kelas: 2, nilai: null, marker: null, r: -1 });
    const ok = cands.filter((x) => x.kelas != null);
    return ok.reduce((b, x) => (x.kelas < b.kelas ? x : b));
  }
  dalilNo(angka, token) {
    const lab = LABEL[token], out = [];
    for (const b of this.t7) if (b.angka_waris.includes(angka) && b.sel[lab] !== undefined) out.push(b.sel[lab]);
    return out;
  }
  token(h) { if (h.nilai_koreksi) return '1/6'; return TOK[h.raw] !== undefined ? TOK[h.raw] : h.raw; }
  row(no, N, frac, raw, kelas, tok) {
    const [k, n] = N[no];
    return { kunci: k, nama: this.nomor[no].nama, jumlah: n, angka: no, hasil_baku: raw, kelas, fraksi_kelompok: frac, fraksi_per_orang: frac.div(n), persen: frac.num() * 100,
      dalil: tok ? (no === 9 && raw === '1/3d+1/3d' ? ['24'] : this.dalilNo(no, tok)) : [] };
  }
  hitung(heirs, harta = null, opsi = {}) {
    const musytarikah = opsi.musytarikah !== false, raddPasangan = opsi.radd_pasangan !== false, radd = opsi.radd !== false;
    const N = {};
    for (const [k, n] of Object.entries(heirs)) { if (n <= 0) continue; const [s, l] = INPUT[k]; N[n === 1 ? s : l] = [k, n]; }
    const res = { status: 'ok', catatan: [], bagian: [], mode: null };
    const present = Object.keys(N).map(Number).sort((a, b) => a - b); const pset = new Set(present);
    if (!present.length) { res.status = 'kosong'; return res; }
    if (pset.has(25) && pset.has(23)) { res.status = 'error'; res.catatan.push('Suami dan istri tidak mungkin sekaligus.'); return res; }
    if (pset.has(23) && N[23][1] > 4) { res.status = 'error'; res.catatan.push('Istri maksimal 4.'); return res; }
    if ((eqSet(pset, [25, 9, 22, 19]) || eqSet(pset, [25, 9, 22, 15])) && present.every((x) => N[x][1] === 1)) {
      const sau = pset.has(19) ? 19 : 15, fr = { 25: new Fr(9, 27), 9: new Fr(6, 27), 22: new Fr(8, 27), [sau]: new Fr(4, 27) };
      res.mode = 'akdariyah'; res.catatan.push('Masalah Akdariyah (Tabel II, asal masalah 27). Cara pakai Tabel II masih dugaan, cocok hasil klasik.');
      for (const no of [...present].reverse()) res.bagian.push(this.row(no, N, fr[no], 'Akdariyah', null, null));
      this.rupiah(res, harta, pset); return res;
    }
    const hb = {}; for (const c of present) hb[c] = this.pilih(c, present);
    if (pset.has(22) && present.some((x) => x >= 14 && x <= 21)) { res.status = 'tidak_didukung'; res.catatan.push('Kakek bersama saudara: butuh Tabel IX (hal. 16) yang belum ada. Konsultasi ahli faraidh.'); return res; }
    if (Object.values(hb).some((h) => h.tipe === 'ashabah_AII')) { res.status = 'tidak_didukung'; res.catatan.push('Hasil AII (Tabel II/IX) di luar Akdariyah belum didukung.'); return res; }
    const fixed = {}; let ashabah = []; let jgh = []; const js = [];
    for (const c of present) {
      const h = hb[c], t = h.tipe;
      if (t === 'mahjub') fixed[c] = ZERO;
      else if (['furudh', 'furudh_plus_sisa', 'furudh_plus_ashabah'].includes(t)) { fixed[c] = frs(h.nilai); if (t !== 'furudh') ashabah.push(c); }
      else if (['ashabah', 'sisa', 'ashabah_AI'].includes(t)) ashabah.push(c);
      else if (t === 'ashabah_bil_ghair') jgh.push(c);
      else if (t === 'gabung_sama_banyak') js.push(c);
      else { res.status = 'tidak_didukung'; res.catatan.push('Tipe ' + t + ' belum didukung'); return res; }
    }
    if (new Set(ashabah).size > 1) { res.status = 'tidak_didukung'; res.catatan.push('Lebih dari satu golongan ashabah tanpa penghalang: belum didukung.'); return res; }
    const pool = {}; for (const c of js) { const r = hb[c].r; (pool[r] = pool[r] || [r]).push(c); }
    let musy = null;
    const kand = present.filter((c) => KANDUNG_LK.has(c) && ['ashabah', 'ashabah_AI'].includes(hb[c].tipe));
    const seib = present.filter((c) => (SEIBU.has(c) && (fixed[c] || ZERO).gt(0)) || (SEIBU.has(c) && js.includes(c)));
    if (musytarikah && kand.length && seib.length) {
      const sisa = ONE.sub(sum(Object.values(fixed)));
      const n_s = seib.reduce((s, c) => s + N[c][1], 0), f_s = sum(seib.map((c) => fixed[c] || ZERO));
      const n_kl = kand.reduce((s, c) => s + N[c][1], 0), kp = jgh.filter((c) => KANDUNG_PR.has(c)), n_kp = kp.reduce((s, c) => s + N[c][1], 0);
      const pos = sisa.gt(0) ? sisa : ZERO, den = 2 * n_kl + n_kp;
      const unit = den ? pos.div(den) : ZERO, per_s = n_s ? f_s.div(n_s) : ZERO;
      if (sisa.le(0) || unit.lt(per_s)) musy = [f_s.add(pos), n_s + n_kl + n_kp, seib, kand, kp];
    }
    const gf = {}; for (const c of present) gf[c] = fixed[c] || ZERO;
    for (const [r, mem] of Object.entries(pool)) { const tot = gf[r], heads = mem.reduce((s, x) => s + N[x][1], 0); for (const x of mem) gf[x] = tot.mul(N[x][1]).div(heads); }
    if (musy) {
      const [pl, heads, sl, kl, kpl] = musy;
      for (const x of [...sl, ...kl, ...kpl]) gf[x] = pl.mul(N[x][1]).div(heads);
      for (const x of [...kl, ...kpl]) ashabah = ashabah.filter((a) => a !== x);
      jgh = jgh.filter((x) => !kpl.includes(x)); res.mode_tambahan = 'musytarikah';
      res.catatan.push('Musytarikah (dalil 25): saudara kandung digabung dengan saudara seibu, berbagi bagian seibu rata per kepala. Hukum ini diperselisihkan antar mazhab; ini menurut metode buku. Bisa dimatikan (musytarikah=False).');
    }
    const Ft = sum(Object.values(gf)); const share = { ...gf };
    if (Ft.gt(1)) { res.mode = 'aul'; res.catatan.push("'Aul (Pasal 192): jumlah bagian " + Ft + ' > 1, penyebut dinaikkan.'); for (const c of Object.keys(share)) share[c] = gf[c].div(Ft); }
    else if (Ft.lt(1)) {
      const sisa = ONE.sub(Ft);
      if (ashabah.length || jgh.length) {
        res.mode = 'sisa'; const w = {};
        for (const c of new Set(ashabah)) w[c] = (jgh.length ? 2 : 1) * N[c][1];
        for (const j of jgh) { const p = hb[j].r; if (w[p] === undefined) w[p] = 2 * N[p][1]; w[j] = N[j][1]; }
        const tw = Object.values(w).reduce((s, x) => s + x, 0);
        for (const [c, wv] of Object.entries(w)) share[c] = (share[c] || ZERO).add(sisa.mul(wv).div(tw));
      } else {
        const recv = present.filter((c) => share[c].gt(0)), sp = recv.filter((c) => c === 23 || c === 25); res.mode = 'radd';
        if (!radd) { res.mode = 'baitulmal'; res.catatan.push('Sisa harta tidak dibagi ke ahli waris (diserahkan ke Baitul Mal, tanpa radd).'); } else if (raddPasangan || !sp.length) { res.catatan.push('Radd (Pasal 193): sisa dibagi berimbang, suami/istri ikut.'); for (const c of Object.keys(share)) share[c] = Ft.gt(0) ? gf[c].div(Ft) : share[c]; }
        else {
          const others = recv.filter((c) => !sp.includes(c)), fo = sum(others.map((c) => gf[c])), spf = sum(sp.map((c) => gf[c]));
          res.catatan.push('Radd tanpa pasangan (opsi).'); for (const c of others) share[c] = gf[c].mul(ONE.sub(spf)).div(fo);
        }
      }
    } else res.mode = 'pas';
    for (const no of [...present].reverse()) { const h = hb[no]; res.bagian.push(this.row(no, N, share[no], h.raw, h.kelas, this.token(h))); }
    res.total = sum(res.bagian.map((b) => b.fraksi_kelompok));
    this.rupiah(res, harta, pset); return res;
  }
  rupiah(res, harta, pset) {
    if (!harta) return;
    const h = Object.assign({ bawaan: 0, bersama: 0, utang: 0, biaya_jenazah: 0, wasiat: 0, wasiat_pecahan: null, wasiat_disetujui: false }, harta);
    const pas = pset.has(23) || pset.has(25), bersama = pas ? Fr.of(h.bersama).div(2) : Fr.of(h.bersama);
    const tir = Fr.of(h.bawaan).add(bersama), net = tir.sub(h.utang).sub(h.biaya_jenazah);
    let w = h.wasiat_pecahan !== null ? Fr.of(h.wasiat_pecahan).mul(net) : Fr.of(h.wasiat); const cap = net.div(3);
    if (w.gt(cap) && !h.wasiat_disetujui) { res.catatan.push('Wasiat dibatasi 1/3 harta bersih (Pasal 195).'); w = cap; }
    const dist = net.sub(w); res.harta = { tirkah: tir, bersih: net, wasiat: w, dibagi: dist, pasangan_hidup: pas };
    if (pas && Fr.of(h.bersama).cmp(0) !== 0) res.catatan.push('Harta bersama dibagi dua dengan pasangan hidup (Pasal 37 UU 1/1974; 1/2 untuk pasangan).');
    for (const b of res.bagian) b.rupiah = b.fraksi_kelompok.mul(dist);
  }
}

/* ---- lapisan lanjut: poligami, pengganti (Pasal 185), waris berantai ---- */
const LAKI = new Set(['anak_lk','cucu_lk','suami','ayah','kakek','sdr_lk_kandung','sdr_lk_seayah','sdr_lk_seibu','kemenakan_kandung','kemenakan_seayah','paman_kandung','paman_seayah','sepupu_paman_kandung','sepupu_paman_seayah']);
const PENGGANTI_OK = new Set(['anak_lk', 'anak_pr', 'cucu_lk', 'cucu_pr']);
class WarisLanjut {
  constructor(d) { this.W = new Waris(d); }
  tirkah(harta, jk, nI, nS) {
    const h = Object.assign({ bawaan: 0, bersama: 0, utang: 0, biaya_jenazah: 0, wasiat: 0, wasiat_pecahan: null, wasiat_disetujui: false }, harta || {}); const cat = [];
    let b = h.bersama, bawaan = Fr.of(h.bawaan), total;
    if (Array.isArray(b)) {
      if (jk === 'L' && b.length > nI) { cat.push('Jumlah isian harta bersama lebih banyak dari istri yang hidup; kelebihan dianggap harta bawaan.'); bawaan = bawaan.add(sum(b.slice(nI).map(Fr.of))); b = b.slice(0, nI); }
      total = sum(b.map(Fr.of));
    } else total = Fr.of(b);
    const pas = nI + nS > 0, milik = pas ? total.div(2) : ZERO;
    const tir = bawaan.add(total).sub(milik), net = tir.sub(h.utang).sub(h.biaya_jenazah);
    let w = h.wasiat_pecahan !== null ? Fr.of(h.wasiat_pecahan).mul(net) : Fr.of(h.wasiat); const cap = net.div(3);
    if (w.gt(cap) && !h.wasiat_disetujui) { cat.push('Wasiat dibatasi 1/3 harta bersih (Pasal 195).'); w = cap; }
    if (pas && !total.eq(0)) cat.push('Harta bersama tiap pernikahan dibagi dua dengan pasangan hidup; separuh pasangan tidak ikut diwariskan.');
    return [{ tirkah: tir, bersih: net, wasiat: w, dibagi: net.sub(w), milik_pasangan: milik }, cat];
  }
  node(node, F, jalur, jk, out, cat, opsi, depth = 0) {
    if (depth > 5) { cat.push(jalur + ': kedalaman waris berantai dibatasi 5 tingkat.'); return false; }
    const heirs = {}; for (const [k, v] of Object.entries(node.heirs || {})) if (v > 0) heirs[k] = v;
    const sesudah = node.wafat_sesudah || [], semua = node.wafat_sebelum || [];
    const sebelum = semua.filter((x) => ((x.keturunan || {}).lk || 0) + ((x.keturunan || {}).pr || 0) > 0);
    for (const x of semua) {
      if (!sebelum.includes(x)) cat.push(jalur + ': ' + x.key + ' wafat sebelum pewaris tanpa keturunan, tidak menjadi ahli waris.');
      if (!PENGGANTI_OK.has(x.key) && sebelum.includes(x)) { cat.push(jalur + ': penggantian untuk ' + x.key + ' belum didukung.'); return false; }
    }
    const comb = { ...heirs }; for (const x of [...sesudah, ...sebelum]) comb[x.key] = (comb[x.key] || 0) + 1;
    if (jk === 'L' && comb.suami) { cat.push(jalur + ': pewaris laki-laki tidak punya suami.'); return false; }
    if (jk === 'P' && comb.istri) { cat.push(jalur + ': pewaris perempuan tidak punya istri.'); return false; }
    const r = this.W.hitung(comb, null, opsi);
    if (r.status !== 'ok') { cat.push(jalur + ': ' + r.status + ' ' + r.catatan.join(' ')); return false; }
    for (const c of r.catatan) cat.push(depth ? jalur + ': ' + c : c);
    for (const b of r.bagian) {
      const k = b.kunci, p = b.fraksi_per_orang, a = heirs[k] || 0;
      if (a) out.push({ jalur, kunci: k, nama: b.nama, jumlah: a, fraksi: p.mul(a).mul(F), dalil: b.dalil, hasil_baku: b.hasil_baku });
      for (const x of sesudah.filter((s) => s.key === k)) {
        if (!this.node(x.node, p.mul(F), jalur + ' > ' + b.nama + ' (wafat sesudah)', LAKI.has(k) ? 'L' : 'P', out, cat, opsi, depth + 1)) return false;
      }
      for (const x of sebelum.filter((s) => s.key === k)) {
        const kt = x.keturunan, unit = 2 * (kt.lk || 0) + (kt.pr || 0), lab = jalur + ' > pengganti ' + b.nama + ' (wafat sebelum pewaris)';
        for (const [g, w, nm] of [['lk', 2, 'Keturunan laki-laki'], ['pr', 1, 'Keturunan perempuan']])
          if (kt[g]) out.push({ jalur: lab, kunci: 'pengganti_' + g, nama: nm, jumlah: kt[g], fraksi: p.mul(F).mul(new Fr(w * kt[g], unit)), dalil: ['Pasal 185 KHI'], hasil_baku: 'pengganti' });
        cat.push(lab + ': batas Pasal 185 ayat 2 (tidak melebihi sederajat) belum dihitung.');
      }
    }
    return true;
  }
  pasangan2(kasus, out, t, sa, nI, res) { const jal = 'Pewaris > ' + (sa.key === 'istri' ? 'Istri' : 'Suami') + ' (wafat sesudah)', rows = out.filter((x) => x.jalur.startsWith(jal)); const Fw = sum(rows.map((x) => x.fraksi)); if (Fw.eq(0)) return; const h = kasus.harta, b = h.bersama, idx = sa.idx != null ? sa.idx : nI - 1, bw = Array.isArray(b) ? Fr.of(b[idx] || 0) : Fr.of(b || 0), half = bw.div(2), own = Fr.of(h.bawaan_pasangan || 0), s1 = Fw.mul(t.dibagi), est = s1.add(half).add(own); for (const x of rows) { const inn = x.fraksi.div(Fw); x.rupiah = inn.mul(est); x.basis = Math.round(est.num()); x.inner = String(inn); x.inner_persen = Math.round(inn.num() * 1e4) / 100; } res.harta2 = { pihak: sa.key, frak: String(Fw), bagian1: Math.round(s1.num()), setengah: Math.round(half.num()), bawaan: Math.round(own.num()), total: Math.round(est.num()) }; } hitung(kasus) {
    const jk = kasus.pewaris.jk, node = kasus.ahli_waris, res = { status: 'ok', catatan: [], bagian: [] }, heirs = node.heirs || {};
    const sA = (node.wafat_sesudah || []).filter((x) => x.key === 'istri' || x.key === 'suami'), nI = (heirs.istri || 0) + sA.filter((x) => x.key === 'istri').length, nS = (heirs.suami || 0) + sA.filter((x) => x.key === 'suami').length, err = (m) => { res.status = 'error'; res.catatan.push(m); return res; };
    if (jk === 'P' && nI) return err('Pewaris perempuan tidak punya istri.'); if (jk === 'L' && nS) return err('Pewaris laki-laki tidak punya suami.');
    if (nI > 4) return err('Istri maksimal 4.'); if (jk === 'P' && nS > 1) return err('Suami maksimal 1.'); if (sA.length > 1) return err('Hanya satu pasangan yang boleh berstatus wafat sesudah pewaris.');
    const opsi = { musytarikah: kasus.musytarikah !== false, radd_pasangan: kasus.radd_pasangan !== false, radd: kasus.radd !== false }, out = [], cat = res.catatan;
    if (!this.node(node, ONE, 'Pewaris', jk, out, cat, opsi)) { res.status = 'tidak_didukung'; return res; }
    res.bagian = out; res.total = sum(out.map((x) => x.fraksi));
    if (sA.length) cat.push('Pasangan wafat sebelum harta dibagi (waris berantai): hasil terdiri dari dua tingkat. Tingkat pertama membagi harta pewaris; bagian pasangan, separuh harta bersama miliknya, dan hartanya sendiri dibagi ke ahli warisnya.'); if (kasus.harta) { const [t, c] = this.tirkah(kasus.harta, jk, nI, nS); cat.push(...c); res.harta = t; for (const x of out) x.rupiah = x.fraksi.mul(t.dibagi); if (sA.length) this.pasangan2(kasus, out, t, sA[0], nI, res); }
    return res;
  }
}
function ringkas(res) {
  const o = { status: res.status, catatan: res.catatan, bagian: [] };
  for (const x of res.bagian || []) {
    const d = {}; for (const [k, v] of Object.entries(x)) if (!['fraksi', 'rupiah', 'fraksi_kelompok', 'fraksi_per_orang'].includes(k)) d[k] = v;
    const f = x.fraksi || x.fraksi_kelompok; d.pecahan = String(f); d.persen = Math.round(f.num() * 1e4) / 100;
    if (x.rupiah) d.rupiah = Math.round(x.rupiah.num()); o.bagian.push(d);
  }
  return o;
}
const API = { Fr, Waris, WarisLanjut, ringkas, INPUT };
if (typeof module !== 'undefined' && module.exports) module.exports = API; else root.WarisJS = API;
})(typeof self !== 'undefined' ? self : this);
