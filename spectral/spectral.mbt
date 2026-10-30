// spectral：全專案的「譜化」層
//
// [D-CharPoly] 特徵多項式 χ_A(x) = det(xI − A) = c₀ + c₁x + … + cₙxⁿ，以 Faddeev–LeVerrier 演算法在 F_p 上算出。
// [D-Spectrum] 譜 = χ_A 在 F_p 中的根與重數；不分裂時「譜」只能以多項式本身表示。
// [T-CH] Cayley–Hamilton：χ_A(A) = 0（本檔以矩陣多項式直接驗算）。
// [T-TrDet] cₙ₋₁ = −tr A，c₀ = (−1)ⁿ det A；分裂時 Σλ = tr A、Πλ = det A。
//
// 譜化的意義：把「結構 + 消元」升級為「結構 + 譜」，於是每個結構都多出
//   (1) 一個完全不變量（特徵多項式，對共軛不變 ⇒ 規範不變）
//   (2) 一個「分類是否足夠」的判準（同譜但不同構 = 譜不完備）。

// ---------------------------------------------------------------------------
// 多項式算術（升幂係數，係數在 F_p）
// ---------------------------------------------------------------------------

///|
pub fn poly_mul(a : Array[Int32], b : Array[Int32], p : Int32) -> Array[Int32] {
  let f = @core.mk_field(p)
  let out : Array[Int32] = Array::make(a.length() + b.length() - 1, 0)
  for i = 0; i < a.length(); i = i + 1 {
    for j = 0; j < b.length(); j = j + 1 {
      out[i + j] = @core.fld_add(f, out[i + j], @core.fld_mul(f, a[i], b[j]))
    }
  }
  out
}

///|
pub fn poly_eval(c : Array[Int32], x : Int32, p : Int32) -> Int32 {
  let f = @core.mk_field(p)
  let mut acc = 0
  let mut i = c.length() - 1
  while i >= 0 {
    acc = @core.fld_add(f, @core.fld_mul(f, acc, x), c[i])
    i = i - 1
  }
  acc
}

///|
/// [E-DivLinear] 以 (x − r) 除多項式；回傳 (商, 餘數)。霍納法的綜合除法。
pub fn poly_div_linear(
  c : Array[Int32],
  r : Int32,
  p : Int32,
) -> (Array[Int32], Int32) {
  let f = @core.mk_field(p)
  let n = c.length() - 1
  let q : Array[Int32] = Array::make(n, 0)
  let mut acc = 0
  let mut i = n
  while i >= 1 {
    acc = @core.fld_add(f, @core.fld_mul(f, acc, r), c[i])
    q[i - 1] = acc
    i = i - 1
  }
  let rem = @core.fld_add(f, @core.fld_mul(f, acc, r), c[0])
  (q, rem)
}

///|
pub fn poly_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    false
  } else {
    let mut ok = true
    for i = 0; i < a.length(); i = i + 1 {
      if a[i] != b[i] {
        ok = false
      }
    }
    ok
  }
}

// ---------------------------------------------------------------------------
// 特徵多項式與譜
// ---------------------------------------------------------------------------

///|
/// [D-Trace] 未約化的跡（Σ 對角元；呼叫者若要比對 F_p 值請用 `mat_trace_mod`）。
pub fn mat_trace(a : @core.Mat) -> Int32 {
  let mut s = 0
  for i = 0; i < a.rows; i = i + 1 {
    s = s + @core.mat_get(a, i, i)
  }
  s
}

///|
/// [D-TraceMod] 模 p 的跡 —— 原始 Σ 可能超過 p（例如 3+6 = 9 ≠ 7），
///   這正是本專案在譜化時抓到的一個 bug：不約化的 tr 與譜和比較會假性失敗。
pub fn mat_trace_mod(a : @core.Mat, p : Int32) -> Int32 {
  @core.fld_norm(@core.mk_field(p), mat_trace(a))
}

///|
/// [E-CharPoly] Faddeev–LeVerrier：M_k = A·M_{k−1} + c_{n−k+1}·I，c_{n−k} = −tr(A·M_k)/k。
///   需要 k 在 F_p 中可逆 ⇒ **p > n**（本檔所有用例皆滿足）。
pub fn char_poly(a : @core.Mat, p : Int32) -> Array[Int32] {
  let n = a.rows
  let f = @core.mk_field(p)
  let c : Array[Int32] = Array::make(n + 1, 0)
  c[n] = 1 % p
  let mut mk = @core.mat_make(n, n, 0)
  for k = 1; k <= n; k = k + 1 {
    let amk = @core.mat_mul(a, mk, p)
    let ck = c[n - k + 1]
    let added = @core.mat_add(
      amk,
      @core.mat_scale(@core.mat_identity(n), ck, p),
      p,
    )
    mk = added
    let tra = mat_trace(@core.mat_mul(a, mk, p))
    let inv_k = @core.fld_inv(f, k % p)
    c[n - k] = @core.fld_neg(f, @core.fld_mul(f, tra, inv_k))
  }
  c
}

///|
/// [E-PolyMat] 以矩陣代入多項式：Σ c_i A^i（Horner 於矩陣環）。
pub fn poly_matrix_eval(
  a : @core.Mat,
  c : Array[Int32],
  p : Int32,
) -> @core.Mat {
  let n = a.rows
  let mut acc = @core.mat_make(n, n, 0)
  let mut i = c.length() - 1
  while i >= 0 {
    acc = @core.mat_add(
      @core.mat_mul(acc, a, p),
      @core.mat_scale(@core.mat_identity(n), c[i], p),
      p,
    )
    i = i - 1
  }
  acc
}

///|
/// [T-CH] Cayley–Hamilton 的直接驗算：χ_A(A) = 0。
pub fn check_cayley_hamilton(a : @core.Mat, p : Int32) -> Bool {
  let c = char_poly(a, p)
  @core.mat_is_zero(poly_matrix_eval(a, c, p))
}

///|
/// [T-TrDet] cₙ₋₁ = −tr A 且 c₀ = (−1)ⁿ det A。
pub fn check_char_poly_coeffs(a : @core.Mat, p : Int32) -> Bool {
  let f = @core.mk_field(p)
  let n = a.rows
  let c = char_poly(a, p)
  let tr = mat_trace(a)
  let det = @core.det_mod(a, f)
  let sign = if n % 2 == 0 { 1 } else { p - 1 }
  c[n] == 1 % p &&
  c[n - 1] == @core.fld_neg(f, tr) &&
  c[0] == @core.fld_mul(f, sign, det)
}

///|
/// [D-SpecRoots] χ_A 在 F_p 中的根與重數（升序、不重覆列出）。
pub fn spectrum_roots(a : @core.Mat, p : Int32) -> Array[(Int32, Int32)] {
  let mut c = char_poly(a, p)
  let out : Array[(Int32, Int32)] = []
  for x = 0; x < p; x = x + 1 {
    if poly_eval(c, x, p) == 0 {
      let mut mult = 0
      let mut cur = c
      // 整除時餘式恆為 0（`poly_eval(cur, x, p) == 0` 已保證），故只取商。
      while poly_eval(cur, x, p) == 0 && cur.length() > 1 {
        let (q, _r) = poly_div_linear(cur, x, p)
        cur = q
        mult = mult + 1
      }
      if mult > 0 {
        out.push((x, mult))
      }
      c = cur
    }
  }
  out
}

///|
/// [D-EigenSpace] 特徵空間維數 dim ker(A − λI) = n − rank(A − λI)。
pub fn eigen_dim(a : @core.Mat, lam : Int32, p : Int32) -> Int32 {
  let f = @core.mk_field(p)
  let ai = @core.mat_add(
    a,
    @core.mat_scale(@core.mat_identity(a.rows), @core.fld_neg(f, lam), p),
    p,
  )
  a.rows - @core.rank_mod(ai, f)
}

///|
/// [D-Split] 譜是否完全分裂於 F_p，以及（分裂時）Σλ 與 Πλ。
pub struct Spectrum {
  dim : Int32
  split : Bool
  trace : Int32
  det : Int32
  roots : Array[(Int32, Int32)]
  sum_roots : Int32
  prod_roots : Int32
  total_mult : Int32
}

///|
pub fn spectrum_of(a : @core.Mat, p : Int32) -> Spectrum {
  let f = @core.mk_field(p)
  let roots = spectrum_roots(a, p)
  let mut sum = 0
  let mut prod = 1
  let mut total = 0
  for (lam, mult) in roots {
    total = total + mult
    for _q = 0; _q < mult; _q = _q + 1 {
      sum = @core.fld_add(f, sum, lam)
      prod = @core.fld_mul(f, prod, lam)
    }
  }
  Spectrum::{
    dim: a.rows,
    split: total == a.rows,
    trace: @core.fld_norm(f, mat_trace(a)),
    det: @core.det_mod(a, f),
    roots,
    sum_roots: sum,
    prod_roots: prod,
    total_mult: total,
  }
}

///|
pub fn spectrum_split(s : Spectrum) -> Bool {
  s.split
}

///|
/// [T-Spec-TrDet] 譜分裂時 Σλ = tr A 且 Πλ = det A。
pub fn check_spectral_tracedet(a : @core.Mat, p : Int32) -> Bool {
  let s = spectrum_of(a, p)
  if !s.split {
    true
  } else {
    s.sum_roots == s.trace && s.prod_roots == s.det
  }
}

///|
/// [T-Spec-Diag] 可對角化 ⟺ 譜分裂且 Σ dim ker(A − λI) = n。
pub fn check_diagonalizable(a : @core.Mat, p : Int32) -> (Bool, Bool) {
  let s = spectrum_of(a, p)
  let mut dims = 0
  for (lam, _m) in s.roots {
    dims = dims + eigen_dim(a, lam, p)
  }
  (s.split, dims == a.rows)
}

///|
/// [T-Spec-Sum-Squares] 可對角化時 rank(A) 不必等於非零譜重數；但
///   tr(A²) = Σ λ²（冪等式的譜版本），本函式驗證後者。
pub fn check_trace_square(a : @core.Mat, p : Int32) -> Bool {
  let f = @core.mk_field(p)
  let a2 = @core.mat_mul(a, a, p)
  let s = spectrum_of(a, p)
  if !s.split {
    true
  } else {
    let mut acc = 0
    for (lam, mult) in s.roots {
      for _q = 0; _q < mult; _q = _q + 1 {
        acc = @core.fld_add(f, acc, @core.fld_mul(f, lam, lam))
      }
    }
    mat_trace_mod(a2, p) == acc
  }
}

// ---------------------------------------------------------------------------
// 結構層：對每個數學結構取譜
// ---------------------------------------------------------------------------

///|
/// [D-Laplacian] 有限圖的 Laplace 矩陣 L = D − A（在 F_p 上）。
pub fn laplacian_of_graph(
  n : Int32,
  edges : Array[(Int32, Int32)],
  p : Int32,
) -> @core.Mat {
  let f = @core.mk_field(p)
  let m = @core.mat_make(n, n, 0)
  for (u, v) in edges {
    m.data[u * n + u] = @core.fld_add(f, m.data[u * n + u], 1)
    m.data[v * n + v] = @core.fld_add(f, m.data[v * n + v], 1)
    m.data[u * n + v] = @core.fld_sub(f, m.data[u * n + v], 1)
    m.data[v * n + u] = @core.fld_sub(f, m.data[v * n + u], 1)
  }
  m
}

///|
/// [T-Spec-Radon] 離散 Radon 變換的 Gram 算子 RᵀR（n²×n²）譜：
///   χ(x) = (x − n)^{n²−1}·(x − (n²+n))，因為 RᵀR = nI + J 而 J 的譜是 {n², 0^{n²−1}}。
pub fn radon_gram_char_poly(n : Int32, p : Int32) -> (Array[Int32], Bool) {
  let r = @radon.mk_radon(n, p)
  let g = @radon.gram_matrix(r)
  let chi = char_poly(g, p)
  // 期望值 (x − n)^{n²−1}(x − n² − n)
  let f = @core.mk_field(p)
  let nc = n * n
  let mut expect : Array[Int32] = [@core.fld_neg(f, n), 1 % p]
  for _i = 1; _i < nc - 1; _i = _i + 1 {
    expect = poly_mul(expect, [@core.fld_neg(f, n), 1 % p], p)
  }
  let last = @core.fld_neg(f, @core.fld_add(f, nc, n))
  expect = poly_mul(expect, [last, 1 % p], p)
  (chi, poly_eq(chi, expect))
}

///|
/// [D-Chirality] 手徵算子 γ_* = γ₁·γ₂·…·γ_d（需要 `@gauge.clifford_available(p)`）。
pub fn chirality_matrix(d : Int32, p : Int32) -> @core.Mat {
  let gs = @gauge.gamma_mats(d, p)
  let sz = @core.int_pow(2, d / 2)
  if gs.length() != d {
    return @core.mat_make(sz, sz, 0)
  }
  let mut acc = @core.mat_identity(sz)
  for g in gs {
    acc = @core.mat_mul(acc, g, p)
  }
  acc
}

///|
/// [T-Spec-Chi] 手徵算子的譜（本專案修正過的版本）：
///   令 s = (−1)^{d(d−1)/2}，則 γ_*² = s·I，且
///     * d 為**奇數**：γ_* 是純量 √s·I ⟹ χ(x) = (x − √s)^m（m = 2^{⌊d/2⌋}）；
///     * d 為**偶數**：χ(x) = (x² − s)^{m/2}，分裂 ⟺ s = +1 或 (s = −1 且 p ≡ 1 mod 4)。
///   舊文件的「χ = (x²+1)^{…}」對奇 d 是錯的（d=3 時 γ_* 純量、χ = (x−√−1)²），
///   已被本函式的前置條件與本測試取代。
pub fn chirality_spectrum(
  d : Int32,
  p : Int32,
) -> (Bool, Bool, Array[(Int32, Int32)]) {
  if !@gauge.clifford_available(p) {
    return (false, false, [])
  }
  let chi = chirality_matrix(d, p)
  let s = spectrum_of(chi, p)
  let sq = @core.mat_mul(chi, chi, p)
  let idn = @core.mat_identity(chi.rows)
  let plus = @core.mat_eq_mod(sq, idn, p)
  (s.split, plus, s.roots)
}

///|
/// [T-Spec-Chi-Formula] χ_{γ_*} 的顯式公式（升幂係數），與 `char_poly` 逐項比對。
///   s = (−1)^{d(d−1)/2}；m = 2^{⌊d/2⌋}。
pub fn check_chirality_formula(d : Int32, p : Int32) -> Bool {
  if !@gauge.clifford_available(p) || p <= 2 * d + 2 {
    return false
  }
  let f = @core.mk_field(p)
  let chi = chirality_matrix(d, p)
  let m = @core.int_pow(2, d / 2)
  let s_neg = d * (d - 1) / 2 % 2 == 1
  // s = +1 或 −1
  let sgn = if s_neg { p - 1 } else { 1 }
  let mut expect : Array[Int32] = [1 % p]
  if d % 2 == 0 {
    // (x² − s)^{m/2}
    let base : Array[Int32] = [@core.fld_neg(f, sgn), 0, 1 % p]
    for _i = 0; _i < m / 2; _i = _i + 1 {
      expect = poly_mul(expect, base, p)
    }
  } else {
    // (x − √s)^m：需要 √s 存在（s = +1 時為 ±1；s = −1 時需 p ≡ 1 mod 4）
    let root = if s_neg {
      match @gauge.pauli_y(p) {
        Some(v) => v
        None => return false
      }
    } else {
      1
    }
    let base : Array[Int32] = [@core.fld_neg(f, root), 1 % p]
    for _i = 0; _i < m; _i = _i + 1 {
      expect = poly_mul(expect, base, p)
    }
  }
  poly_eq(char_poly(chi, p), expect)
}

///|
/// [T-Spec-Lap-Cycle] C_n 的 Laplace 譜：{2 − ω^k − ω^{−k} : k = 0..n−1}，
///   ω 為 F_p 中的 n 次本原根（需 n | p−1）。tr L = 2n、det L = 0。
pub fn check_cycle_laplacian_spectrum(n : Int32, p : Int32) -> Bool {
  let w = @radon.root_of_unity(n, p)
  if w == 1 && n > 1 {
    return false
  }
  let f = @core.mk_field(p)
  let edges : Array[(Int32, Int32)] = []
  for i = 0; i < n; i = i + 1 {
    edges.push((i, (i + 1) % n))
  }
  let l = laplacian_of_graph(n, edges, p)
  let chi = char_poly(l, p)
  let mut expect : Array[Int32] = [1 % p]
  for k = 0; k < n; k = k + 1 {
    let wk = @core.mod_pow(w, k, p)
    let wki = @core.mod_pow(w, n - k, p)
    let lam = @core.fld_sub(f, 2 % p, @core.fld_add(f, wk, wki))
    expect = poly_mul(expect, [@core.fld_neg(f, lam), 1 % p], p)
  }
  poly_eq(chi, expect) && mat_trace_mod(l, p) == 2 * n % p
}

///|
/// [T-Spec-Perm] 置換矩陣的特徵多項式 = Π_cycles (x^{len} − 1)。
///   本函式以「由置換建矩陣 → 算 χ」與「由循環型直接乘出多項式」兩條路徑互相比對。
pub fn check_perm_char_poly(perm : Array[Int32], p : Int32) -> Bool {
  let n = perm.length()
  let m = @core.mat_make(n, n, 0)
  for i = 0; i < n; i = i + 1 {
    m.data[i * n + perm[i]] = 1 % p
  }
  let chi = char_poly(m, p)
  // 循環分解
  let seen : Array[Bool] = Array::make(n, false)
  let mut expect : Array[Int32] = [1 % p]
  let f = @core.mk_field(p)
  for i = 0; i < n; i = i + 1 {
    if !seen[i] {
      let mut len = 0
      let mut j = i
      while !seen[j] {
        seen[j] = true
        j = perm[j]
        len = len + 1
      }
      // (x^len − 1)
      let factor : Array[Int32] = Array::make(len + 1, 0)
      factor[len] = 1 % p
      factor[0] = @core.fld_neg(f, 1)
      expect = poly_mul(expect, factor, p)
    }
  }
  poly_eq(chi, expect)
}

///|
/// [D-GraphDiam] 無權圖的直徑（Floyd–Warshall；不連通回傳 −1）。
pub fn graph_diam(n : Int32, edges : Array[(Int32, Int32)]) -> Int32 {
  let inf = 1000000
  let d : Array[Array[Int32]] = Array::makei(n, _ => Array::make(n, inf))
  for i = 0; i < n; i = i + 1 {
    d[i][i] = 0
  }
  for (u, v) in edges {
    d[u][v] = 1
    d[v][u] = 1
  }
  for m = 0; m < n; m = m + 1 {
    for i = 0; i < n; i = i + 1 {
      for j = 0; j < n; j = j + 1 {
        if d[i][m] + d[m][j] < d[i][j] {
          d[i][j] = d[i][m] + d[m][j]
        }
      }
    }
  }
  let mut best = 0
  let mut disconnected = false
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      if d[i][j] >= inf {
        disconnected = true
      } else if d[i][j] > best {
        best = d[i][j]
      }
    }
  }
  if disconnected {
    -1
  } else {
    best
  }
}

///|
/// [D-Adjacency] 有限圖的鄰接矩陣。
pub fn adjacency_of_graph(
  n : Int32,
  edges : Array[(Int32, Int32)],
  p : Int32,
) -> @core.Mat {
  let f = @core.mk_field(p)
  let m = @core.mat_make(n, n, 0)
  for (u, v) in edges {
    m.data[u * n + v] = @core.fld_add(f, m.data[u * n + v], 1)
    m.data[v * n + u] = @core.fld_add(f, m.data[v * n + u], 1)
  }
  m
}

///|
/// [T-Spec-Isospectral] 譜**不**決定結構：K_{1,4}（星形）與 C₄ ⊔ K₁ 的**鄰接**譜相同
///   （皆為 {±2, 0,0,0}），但直徑一個是 2、一個是 ∞（不連通）⟹ 由譜不能恢復度量結構。
///   （注意：這兩者的 **Laplace** 譜其實不同 —— 這是本專案在譜化時抓到的一個易錯點。）
///   回傳 (同譜, 星形直徑, 四邊形+孤立點直徑)。
pub fn isospectral_star_vs_cycle(p : Int32) -> (Bool, Int32, Int32) {
  let star : Array[(Int32, Int32)] = [(0, 1), (0, 2), (0, 3), (0, 4)]
  let cyc : Array[(Int32, Int32)] = [(0, 1), (1, 2), (2, 3), (3, 0)]
  let chi_s = char_poly(adjacency_of_graph(5, star, p), p)
  let chi_c = char_poly(adjacency_of_graph(5, cyc, p), p)
  (poly_eq(chi_s, chi_c), graph_diam(5, star), graph_diam(5, cyc))
}

///|
/// [D-Projector] 冪等矩陣（投影）的譜 ⊆ {0,1}，且 tr P = rank P（冪等矩陣的秩等於跡）。
pub fn check_idempotent_theorem(
  a : @core.Mat,
  p : Int32,
) -> (Bool, Bool, Int32, Int32) {
  let f = @core.mk_field(p)
  let a2 = @core.mat_mul(a, a, p)
  let idem = @core.mat_eq_mod(a2, a, p)
  let s = spectrum_of(a, p)
  let mut only01 = true
  for (lam, _m) in s.roots {
    if lam != 0 && lam != 1 % p {
      only01 = false
    }
  }
  (idem, only01, @core.fld_norm(f, mat_trace(a)), @core.rank_mod(a, f))
}

///|
/// [D-CellMatrix] 超結構的「單元格大小矩陣」M[a][b] = |a ⋆ b| —— 超化的譜化入口。
pub fn hyper_cell_matrix(h : @hyper.Hyper) -> @core.Mat {
  let n = @hyper.hyper_size(h)
  let m = @core.mat_make(n, n, 0)
  for a = 0; a < n; a = a + 1 {
    for b = 0; b < n; b = b + 1 {
      m.data[a * n + b] = @hyper.hyper_cell_size(h, a, b)
    }
  }
  m
}

///|
/// [T-Spec-Conj] 譜在共軛下不變：χ_{PAP⁻¹} = χ_A。
///   用「置換矩陣」與「剪切矩陣」兩類可逆 P 各驗一次。
pub fn check_spectral_conjugation(a : @core.Mat, p : Int32) -> Bool {
  let n = a.rows
  let f = @core.mk_field(p)
  let chi = char_poly(a, p)
  // P1：循環置換
  let perm : Array[Int32] = Array::makei(n, i => (i + 1) % n)
  let pinv : Array[Int32] = Array::makei(n, i => (i + n - 1) % n)
  let mk = fn(pp : Array[Int32]) -> @core.Mat {
    let m = @core.mat_make(n, n, 0)
    for i = 0; i < n; i = i + 1 {
      m.data[i * n + pp[i]] = 1 % p
    }
    m
  }
  let pm = mk(perm)
  let pmi = mk(pinv)
  let conj1 = @core.mat_mul(@core.mat_mul(pm, a, p), pmi, p)
  // P2：上三角剪切 I + E01
  let shear = @core.mat_add(
    @core.mat_identity(n),
    @core.mat_build(n, n, (i, j) => if i == 0 && j == 1 { 1 % p } else { 0 }),
    p,
  )
  let shear_inv = @core.mat_add(
    @core.mat_identity(n),
    @core.mat_scale(
      @core.mat_build(n, n, (i, j) => if i == 0 && j == 1 { 1 % p } else { 0 }),
      @core.fld_neg(f, 1),
      p,
    ),
    p,
  )
  let conj2 = @core.mat_mul(@core.mat_mul(shear, a, p), shear_inv, p)
  poly_eq(char_poly(conj1, p), chi) && poly_eq(char_poly(conj2, p), chi)
}

///|
/// [D-RegularRep] 扭曲群代數 A^ω 的左正則表示：ρ_reg(a)[b][a+b] = ζ^{ω(a,b)}。
///   [T-Spec-RegularRep] 由於左乘無不動點（a ≠ e），tr ρ_reg(a) = 0；而 tr ρ_reg(e) = |G|。
pub fn regular_rep_matrix(
  o : @twist.Omega,
  a : Array[Int32],
  p : Int32,
) -> @core.Mat {
  let g = @twist.omega_group(o)
  let n = @twist.grp_order(g)
  let m = @core.mat_make(n, n, 0)
  for bc = 0; bc < n; bc = bc + 1 {
    let b = @twist.grp_of_code(g, bc)
    let sum = @twist.grp_add(g, a, b)
    let sc = @twist.grp_code(g, sum)
    // omega_get 回傳的是**指數** ω(a,b) ∈ ℤ/ℓ，故矩陣元素為 ζ^{ω(a,b)}
    m.data[bc * n + sc] = @core.mod_pow(
      @twist.omega_zeta(o),
      @twist.omega_get(o, @twist.grp_code(g, a), bc),
      p,
    )
  }
  m
}

///|
/// [T-Spec-RegularRep] tr ρ_reg(e) = |G|，其餘為 0 ⟹ 跡分離出單位元（而譜不能：ρ 的譜在多數情況下相同）。
pub fn check_regular_rep_trace(o : @twist.Omega, p : Int32) -> (Int32, Int32) {
  let g = @twist.omega_group(o)
  let n = @twist.grp_order(g)
  let f = @core.mk_field(p)
  let id = @twist.grp_zero(g)
  let mut tr_identity = 0
  let mut nonzero_others = 0
  for code = 0; code < n; code = code + 1 {
    let a = @twist.grp_of_code(g, code)
    let t = @core.fld_norm(f, mat_trace(regular_rep_matrix(o, a, p)))
    if a == id {
      tr_identity = t
    } else if t != 0 {
      nonzero_others = nonzero_others + 1
    }
  }
  (tr_identity, nonzero_others)
}

// ---------------------------------------------------------------------------
// 投影算子：冪等矩陣的譜
// ---------------------------------------------------------------------------

///|
/// [E-MatInv] F_p 上的矩陣反演：逐列解 A x = e_j（走 core 的消元）。
pub fn mat_inverse(a : @core.Mat, p : Int32) -> @core.Mat? {
  let f = @core.mk_field(p)
  let n = a.rows
  if @core.rank_mod(a, f) != n {
    return None
  }
  let inv = @core.mat_make(n, n, 0)
  for j = 0; j < n; j = j + 1 {
    let e : Array[Int32] = Array::make(n, 0)
    e[j] = 1 % p
    match @core.solve_linear(a, e, f) {
      Some(x) =>
        for i = 0; i < n; i = i + 1 {
          inv.data[i * n + j] = x[i]
        }
      None => return None
    }
  }
  Some(inv)
}

///|
/// [D-Projector] P = A(AᵀA)⁻¹Aᵀ（正交投影到 A 的行空間）：P² = P、tr P = rank A。
pub fn projector(a : @core.Mat, p : Int32) -> @core.Mat? {
  let at = @core.mat_transpose(a)
  let ata = @core.mat_mul(at, a, p)
  match mat_inverse(ata, p) {
    Some(gram_inv) => {
      let left = @core.mat_mul(a, gram_inv, p)
      Some(@core.mat_mul(left, at, p))
    }
    None => None
  }
}
