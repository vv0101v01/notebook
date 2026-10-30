///| ## evolve —— 演變（evolution）與恆定關係（invariant relations）的自動推導

///|

///| 想法：把前面各模块的結構放在一個「演變」之下（翻轉、gauge 流、Radon 平滑、

///| SL₂ 剪切、尺度增長），在每一步記錄一組候選量（Ledger），然後

///|   [D-Derive] 用消元在上同調意義下求「觀測向量空間的核」= 全部線性恆等式，

///|   並在整數（或 mod p）上逐點復核，最後把得到的關係拿到**另一組獨立資料**上驗證。

///| 這樣「記錄恆定關係 → 推導新定理」這一步本身也是可計算、可驗證的。
// ===================== Ledger 與關係推導 =====================

///|
/// [D-RowSet] 演變過程中每一步的觀測值（每列一步，欄為候選量；
///   若含常數欄 1，则可表達仿射關係）。
pub struct RowSet {
  rows : Array[Array[Int32]]
}

///|
pub fn rowset_of(rows : Array[Array[Int32]]) -> RowSet {
  RowSet::{ rows, }
}

///|
/// [D-LedgerConst] 在左側加一欄常數 1（允許常數項）。
pub fn rowset_with_const(rows : Array[Array[Int32]]) -> RowSet {
  RowSet::{
    rows: Array::makei(rows.length(), i => {
      let r = rows[i]
      Array::makei(r.length() + 1, j => if j == 0 { 1 } else { r[j - 1] })
    }),
  }
}

///|
pub fn rowset_len(l : RowSet) -> Int32 {
  l.rows.length()
}

///|
/// [D-Rows] 取出全部列（供 ledger 等下游套件取用）。
pub fn rowset_rows(l : RowSet) -> Array[Array[Int32]] {
  l.rows
}

///|
/// [D-LinComb] c·row（逐點內積）。
pub fn dot(c : Array[Int32], row : Array[Int32]) -> Int32 {
  let mut s = 0
  let mut i = 0
  while i < c.length() {
    s = s + c[i] * row[i]
    i = i + 1
  }
  s
}

///|
/// [D-RelExact] 關係 c 在 ℤ 上於每一步成立。
pub fn holds_exact(l : RowSet, c : Array[Int32]) -> Bool {
  l.rows.all(row => dot(c, row) == 0)
}

///|
/// [D-RelMod] 關係 c 在 F_p 上於每一步成立。
pub fn holds_mod(l : RowSet, c : Array[Int32], p : Int32) -> Bool {
  l.rows.all(row => @core.vec_dot(c, row, p) == 0)
}

///|
fn normalize(c : Array[Int32], p : Int32) -> Array[Int32] {
  // 最小絕對代表 + 首個非零係數為正
  let v = Array::makei(c.length(), i => {
    let x = c[i] % p
    if x > p / 2 {
      x - p
    } else if x < 0 - p / 2 {
      x + p
    } else {
      x
    }
  })
  let mut g = 0
  for x in v {
    g = @core.igcd(if g < 0 { 0 - g } else { g }, if x < 0 { 0 - x } else { x })
  }
  let gg = if g == 0 { 1 } else { g }
  let out = Array::makei(v.length(), i => v[i] / gg)
  let mut k = 0
  while k < out.length() {
    if out[k] != 0 {
      if out[k] < 0 {
        return Array::makei(out.length(), i => 0 - out[i])
      } else {
        return out
      }
    }
    k = k + 1
  }
  out
}

///|
/// [D-Derive] 從 Ledger 導出全部線性恆等式（兩階段）：
///   (1) 消元：對觀測矩陣取 F_p 零空間，得所有 mod-p 關係；
///   (2) 提升與飽和：把基向量取最小絕對代表、約簡 gcd，逐條在 ℤ（exact=true）
///       或 F_p 上復核；保留通過者，再以兩兩和/差做整格飽和（同樣需復核通過），
///       使「同一關係的不同整數組合」也被納入——這一步讓導出結果對基的選擇不敏感。
///   因每條關係都經過代回檢驗，不會產生偽關係。
pub fn derive_relations(
  l : RowSet,
  p : Int32,
  exact : Bool,
) -> Array[Array[Int32]] {
  let m = @core.mat_from_rows(l.rows)
  let fld = @core.mk_field(p)
  let basis = @core.nullspace_basis(m, fld)
  // 候選池：先放零空間基（取最小絕對代表），再做兩輪兩兩加減closure
  let pool : Array[Array[Int32]] = []
  let add_cand = (c : Array[Int32]) => {
    if c.any(x => x != 0) && pool.length() < 64 {
      let _ = pool.push(normalize(c, p))
    }
  }
  for b in basis {
    add_cand(b)
  }
  let mut round = 0
  while round < 2 {
    let k = pool.length()
    let mut i2 = 0
    while i2 < k {
      let mut j2 = i2 + 1
      while j2 < k {
        add_cand(add_vec(pool[i2], pool[j2]))
        add_cand(sub_vec(pool[i2], pool[j2]))
        j2 = j2 + 1
      }
      i2 = i2 + 1
    }
    round = round + 1
  }
  // 復核 + 極小化（只保留代回成立且線性獨立者）
  let out : Array[Array[Int32]] = []
  for c in pool {
    if accepts(l, c, p, exact, out) {
      let _ = out.push(c)
    }
  }
  out
}

///|
fn add_vec(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  Array::makei(a.length(), i => a[i] + b[i])
}

///|
fn sub_vec(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  Array::makei(a.length(), i => a[i] - b[i])
}

///|
fn accepts(
  l : RowSet,
  c : Array[Int32],
  p : Int32,
  exact : Bool,
  have : Array[Array[Int32]],
) -> Bool {
  let ok_rel = if exact { holds_exact(l, c) } else { holds_mod(l, c, p) }
  if !ok_rel {
    return false
  }
  if have.length() == 0 {
    return true
  }
  // 已張出則不重複收（保持關係集極小）
  let fld = @core.mk_field(p)
  let r0 = @core.rank_mod(@core.mat_from_rows(have), fld)
  let more = have.copy()
  let _ = more.push(c)
  @core.rank_mod(@core.mat_from_rows(more), fld) > r0
}

///|
/// [D-Find] 目標關係是否屬於「導出關係」在 F_p 上張成的空間
///   （即：是否可由消元得到的關係線性組合出來；rank 判準）。
pub fn relation_derived(
  rels : Array[Array[Int32]],
  target : Array[Int32],
  p : Int32,
) -> Bool {
  if rels.length() == 0 {
    false
  } else {
    let fld = @core.mk_field(p)
    let base = @core.mat_from_rows(rels)
    let r0 = @core.rank_mod(base, fld)
    let rows2 = rels.copy()
    let _ = rows2.push(target)
    let r1 = @core.rank_mod(@core.mat_from_rows(rows2), fld)
    r0 == r1
  }
}

///|
/// [T-Evolve-Stage] 一段演變的完整驗證（科學方法的可執行版本）：
///   在資料族 A 上「用消元導出」候選恆等式，確認目標關係屬於導出結果；
///   再把目標關係拿到獨立資料族 B 上做「轉移檢驗」。
///   （A 上偶然成立的關係会在 B 上被拒，故轉移檢驗只以目標關係為準；
///    各家族的全部導出關係是否都能轉移，則由各自的測試單獨審查。）
///   回傳 (目標關係被導出, 目標關係在 B 上仍恆定)。
pub fn check_derived_then_transfer(
  a : RowSet,
  b : RowSet,
  p : Int32,
  exact : Bool,
  target : Array[Int32],
) -> (Bool, Bool) {
  let rels = derive_relations(a, p, exact)
  let found = relation_derived(rels, target, p)
  let holds_on_b = if exact {
    holds_exact(b, target)
  } else {
    holds_mod(b, target, p)
  }
  (found, holds_on_b)
}

// ===================== 演變一：associahedron 翻轉（nc）=====================

///|
/// [E-Flip] 在 n-gon 三角剖分的翻轉圖上随機漫遊 steps 步，
///   每步記錄 (三角數, 對偶圖頂點數, 對偶圖邊數, 最大度, 對角線交叉對數)。
/// [Inv-Flip] 恆定關係：E_dual = V_dual - 1（對偶是樹）、交叉對數 = 0、
///   三角數 = 對偶頂點數 = n-2。
pub fn evolve_flips(n : Int32, steps : Int32, seed : Int32) -> RowSet {
  let all = @nc.triangulations(n)
  let rng = @core.rng_seed(seed)
  let mut cur = 0
  let rows : Array[Array[Int32]] = []
  let mut t = 0
  while t <= steps {
    let diags = all[cur]
    let tris = @nc.triangles_of(n, diags)
    let dual = @nc.dual_graph(tris, diags)
    let md = @nc.max_degree(tris.length(), dual)
    let mut cross = 0
    let m = diags.length()
    let mut i = 0
    while i < m {
      let mut j = i + 1
      while j < m {
        if @nc.chords_cross(diags[i], diags[j]) {
          cross = cross + 1
        }
        j = j + 1
      }
      i = i + 1
    }
    let _ = rows.push([
      tris.length(),
      tris.length(),
      @nc.dual_edge_count(dual),
      md,
      cross,
    ])

    // 隨機走一步到一個可翻轉的鄰居
    let neigh : Array[Int32] = []
    let mut k = 0
    while k < all.length() {
      if @nc.are_flippable(all[cur], all[k]) {
        let _ = neigh.push(k)
      }
      k = k + 1
    }
    if neigh.length() > 0 {
      cur = neigh[@core.rng_below(rng, neigh.length())]
    }
    t = t + 1
  }
  rowset_with_const(rows)
}

// ===================== 演變二：coboundary gauge 流（twist）=====================

///|
/// [E-Gauge] 從 Clifford cocycle 出發，反覆施加隨機規範變換，
///   每步記錄 (|G|, |rad|, dim Z(A^ω), d²·|rad|, Σ_{a,b} ω(a,b))（最後一个是可變量）。
/// [Inv-Gauge] 恆定關係：dim Z = |rad|、d²·|rad| = |G|（K₀ 秩與維數公式沿规範流守恆）。
pub fn evolve_gauge(d : Int32, steps : Int32, seed : Int32) -> RowSet {
  let g = @twist.grp(Array::makei(d, _ => 2))
  let p = 5
  let n = @twist.grp_order(g)
  let rng = @core.rng_seed(seed)
  let mut o = @twist.mk_omega(g, 2, p, @gauge.clifford_cocycle_vec(d))
  let rows : Array[Array[Int32]] = []
  let mut t = 0
  while t <= steps {
    let rad = @twist.omega_radical_size(o)
    let cd = @twist.center_dim(o)
    let dsq = @twist.tw_irrep_dim_sq(o)
    let mut ssum = 0
    for x in o.w {
      ssum = ssum + x
    }
    let _ = rows.push([n, rad, cd, dsq * rad, ssum])
    // 隨機規範變換
    let mu = Array::makei(n, i => {
      if i == 0 {
        0
      } else {
        @core.rng_below(rng, 2)
      }
    })
    o = @twist.omega_with_w(o, @twist.omega_gauge(o, mu))
    t = t + 1
  }
  rowset_of(rows)
}

// ===================== 演變三：Radon 平滑 =====================

///|
/// [E-Radon] f ⟼ S f := (1/n)·RᵀR f（mod p）；每步記錄
///   (Σf², Σ(Rf)², (Σf)²)（皆 mod p）。
/// [Inv-Radon] 恆定關係：Σ(Rf)² − n·Σf² − (Σf)² = 0（每一步都成立 ⟹ S 迭代下的二次型守恆律）。
pub fn evolve_radon(
  n : Int32,
  p : Int32,
  steps : Int32,
  seed : Int32,
) -> RowSet {
  let r = @radon.mk_radon(n, p)
  let m = @radon.radon_matrix(r)
  let mt = @core.mat_transpose(m)
  let inv_n = @core.fld_inv(@core.mk_field(p), n)
  let rng = @core.rng_seed(seed)
  let nc = n * n
  let mut f = Array::makei(nc, _ => @core.rng_below(rng, p))
  let rows : Array[Array[Int32]] = []
  let mut t = 0
  while t <= steps {
    let mf = @core.mat_mul_vec(m, f, p)
    let mut q0 = 0
    for x in f {
      q0 = (q0 + x * x % p) % p
    }
    let mut q1 = 0
    for x in mf {
      q1 = (q1 + x * x % p) % p
    }
    let mut s = 0
    for x in f {
      s = (s + x) % p
    }
    let _ = rows.push([q0, q1, s * s % p])
    // f ← (1/n)·RᵀR f
    let g = @core.mat_mul_vec(mt, mf, p)
    f = @core.vec_scale(g, inv_n, p)
    t = t + 1
  }
  rowset_of(rows)
}

// ===================== 演變四：SL₂ 剪切（tensor）=====================

///|
/// [E-Shear] 對 T ∈ F_p^{2×2×2} 施加 mode-0 初等剪切 T'_{0jk} = T_{0jk} + c·T_{1jk}，
///   每步記錄 (Det(T), Det(T'))。
/// [Inv-Shear] 恆定關係：Det(T') − Det(T) = 0 —— Cayley 超行列式是 SL₂³-不變量。
pub fn evolve_shear(p : Int32, steps : Int32, seed : Int32) -> RowSet {
  let rng = @core.rng_seed(seed)
  let mut t = @tensor.t3_of(2, 2, 2, p, (_i, _j, _k) => @core.rng_below(rng, p))
  let rows : Array[Array[Int32]] = []
  let mut it = 0
  while it <= steps {
    let d0 = @tensor.hyperdet222(t)
    let c = @core.rng_below(rng, p)
    let t2 = @tensor.t3_of(2, 2, 2, p, (i, j, k) => {
      if i == 0 {
        (@tensor.t3_get(t, 0, j, k) + c * @tensor.t3_get(t, 1, j, k)) % p
      } else {
        @tensor.t3_get(t, 1, j, k)
      }
    })
    let d1 = @tensor.hyperdet222(t2)
    let _ = rows.push([d0, d1])
    t = t2
    it = it + 1
  }
  rowset_of(rows)
}

// ===================== 演變五：VR 尺度增長（metric）=====================

///|
/// [E-VR] 沿尺度 r = 1,2,… 增長；每步記錄 (V, E, F, β0, β1, χ_simplicial)。
/// [Inv-VR] 恆定關係：V − E + F − (β0 − β1) = 0（Euler），且 β0 ≡ 1（連通性不變）。
pub fn evolve_vr(n : Int32, rmax : Int32) -> RowSet {
  // （保留原行序，行內容在下方重建）
  let sp = @metric.mspace_cycle(n, 1)
  let rows : Array[Array[Int32]] = []
  let mut r = 1
  while r <= rmax {
    let sims = @metric.vr_simplices(sp, r)
    let b = @metric.vr_betti_all(sp, r)
    let get = fn(i : Int32) -> Int32 { if i < b.length() { b[i] } else { 0 } }
    let fv = @metric.vr_f_vector(sims, n - 1)
    let chi_s = @metric.alt_sum(fv)
    let chi_b = @metric.alt_sum(b)
    let _ = rows.push([chi_s, chi_b, get(0), get(1)])
    r = r + 1
  }
  rowset_with_const(rows)
}

// ===================== 由資料得出的新定理（可執行版本）=====================

///|
/// [T-Evolve-Summary] 五條演化各自的核心關係，全部「先導出、後轉移驗證」。
///   回傳五個 (found, transfers) 對。
pub fn evolve_summary() -> Array[Bool] {
  let out : Array[Bool] = []
  // 1) flips: E - V + 1 = 0（欄位 (T, V, E, Δ, cross) → 目標 (0,-1,1,0,0) 加常數欄後 (1,-1,1,0,0)? 用無常數欄版本）
  let la = evolve_flips(5, 12, 11)
  let lb = evolve_flips(6, 12, 12)
  let (f1, t1) = check_derived_then_transfer(la, lb, 10007, true, [
    1, 0, -1, 1, 0, 0,
  ])
  let _ = out.push(f1)
  let _ = out.push(t1)
  // 2) gauge: dim Z - |rad| = 0，欄位 (|G|, rad, cd, dsq*rad, Σω)
  let ga = evolve_gauge(3, 10, 21)
  let gb = evolve_gauge(4, 10, 22)
  let (f2, t2) = check_derived_then_transfer(ga, gb, 10007, true, [
    0, -1, 1, 0, 0,
  ])
  let _ = out.push(f2)
  let _ = out.push(t2)
  // 3) radon: Σ(Rf)² - n·Σf² - (Σf)² = 0（欄位 (Σf², Σ(Rf)², (Σf)²)，n=3）
  let p3 = 10007
  let ra = evolve_radon(3, p3, 8, 31)
  let rb = evolve_radon(3, p3, 8, 32)
  let (f3, t3) = check_derived_then_transfer(ra, rb, p3, false, [-3, 1, -1])
  let _ = out.push(f3)
  let _ = out.push(t3)
  // 4) shear: Det 不變
  let sa = evolve_shear(3, 10, 41)
  let sb = evolve_shear(5, 10, 42)
  let (f4, t4) = check_derived_then_transfer(sa, sb, 10007, true, [-1, 1])
  let _ = out.push(f4)
  let _ = out.push(t4)
  // 5) VR: Euler 恆等式 χ_simplicial - χ_betti = 0（欄位 (1, χ_s, χ_b, β0, β1)）
  let va = evolve_vr(5, 2)
  let vb = evolve_vr(7, 3)
  let (f5, t5) = check_derived_then_transfer(va, vb, 10007, true, [
    0, 1, -1, 0, 0,
  ])
  let _ = out.push(f5)
  let _ = out.push(t5)
  out
}
