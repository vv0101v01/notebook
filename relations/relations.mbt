// relations：五種關係算子 —— 相對（relative）· 對偶（dual）· 對比（contrast）· 蘊含（implication）· 比率（ratio）
//
// 這五個算子的共同目的：**由已有的定理／結構自動收集新定理與算法**。
//   * 相對：以基準把量正規化，得到「轉移後仍不變」的比值（[T-Rel-Scale]）。
//   * 對偶：把一個陳述換成對偶陳述（矩陣轉置、上鏈／下鏈、指標置換、原像／餘核）。
//   * 對比：兩族現象的差集 —— 只在 A 成立、只在 B 成立、兩者皆成立。
//   * 蘊含：在有限模型上判定 p ⟹ q（無反例即成立），並求傳遞閉包與等價類。
//   * 比率：一族比值恆定時給出該常數（約分後），是「量綱不變量」的離散版本。

// ---------------------------------------------------------------------------
// 記錄型別：所有收集到的關係都寫成 Rec，可再灌進持久賬本
// ---------------------------------------------------------------------------

///|
/// [D-Rec] 一條收集到的關係。`kind`：0 相對、1 對偶、2 對比、3 蘊含、4 比率。
pub struct Rec {
  kind : Int32
  a : Int32
  b : Int32
  holds : Bool
}

///|
pub fn rec(kind : Int32, a : Int32, b : Int32, holds : Bool) -> Rec {
  Rec::{ kind, a, b, holds, }
}

///|
/// [D-RecValues] 把記錄壓成可入賬的整數列：(kind, a, b, holds)。
pub fn rec_values(r : Rec) -> Array[Int32] {
  [r.kind, r.a, r.b, if r.holds { 1 } else { 0 }]
}

// ---------------------------------------------------------------------------
// 1) 相對 relative
// ---------------------------------------------------------------------------

///|
/// [D-Rel] 相對值 a/b（F_p 上的比值）。
pub fn relative(a : Int32, b : Int32, p : Int32) -> Int32 {
  @core.fld_div(@core.mk_field(p), a, b)
}

///|
/// [D-RelProfile] 相對剖面：每一項除上第一項（基準）。
pub fn relative_profile(xs : Array[Int32], p : Int32) -> Array[Int32] {
  if xs.length() == 0 {
    return []
  }
  let base = xs[0]
  Array::makei(xs.length(), i => relative(xs[i], base, p))
}

///|
/// [T-Rel-Scale] 若 ys = c·xs（逐項同倍數），則兩者的相對剖面相同 ——
///   這就是「相對」作為不變量的意義：它抹掉整體尺度。
pub fn check_relative_scale_invariance(
  xs : Array[Int32],
  c : Int32,
  p : Int32,
) -> Bool {
  let ys = xs.map(x => @core.fld_mul(@core.mk_field(p), x, c))
  relative_profile(xs, p) == relative_profile(ys, p)
}

// ---------------------------------------------------------------------------
// 2) 對偶 dual
// ---------------------------------------------------------------------------

///|
/// [T-Dual-Rank] 列秩 = 行秩：rank(A) = rank(Aᵀ)，且
///   nullity(A) − nullity(Aᵀ) = cols − rows（「指標」）。
///   注意兩個零化度**不相等**（除非方陣）——這是本專案在收集對偶關係時修正過的一條：
///   原版誤寫成「nullity 相同」，對長方形矩陣是錯的。
pub fn dual_rank_nullity(m : @core.Mat, p : Int32) -> Bool {
  let f = @core.mk_field(p)
  let r1 = @core.rank_mod(m, f)
  let r2 = @core.rank_mod(@core.mat_transpose(m), f)
  let nullity_a = m.cols - r1
  let nullity_at = m.rows - r2
  r1 == r2 && nullity_a - nullity_at == m.cols - m.rows
}

///|
/// [T-Dual-Chain] 下鏈／上鏈對偶：δ^k = (∂_{k+1})ᵀ，且 dim H^k = dim H_k。
///   本函式用兩條獨立路徑算維數：
///     H_k  : dim C_k − rank ∂_k − rank ∂_{k+1}
///     H^k  : dim C_k − rank δ^k − rank δ^{k−1}（δ 為轉置矩陣，秩由獨立的消元得出）
///   回傳 (∂∂ = 0, 同調維數 == 上同調維數)。
pub fn dual_chain_cochain(
  m : @metric.MSpace,
  r : Int32,
  p : Int32,
) -> (Bool, Bool) {
  let f = @core.mk_field(p)
  let sims = @metric.vr_simplices(m, r)
  let b0 = @metric.boundary_matrix(sims, 0)
  let b1 = @metric.boundary_matrix(sims, 1)
  let b2 = @metric.boundary_matrix(sims, 2)
  // 複形的基本性質：∂_{k}∘∂_{k+1} = 0
  let dd = @core.mat_is_zero(@core.mat_mul(b0, b1, p)) &&
    @core.mat_is_zero(@core.mat_mul(b1, b2, p))
  // 各維度的 simplex 數
  let c0 = @metric.simplices_of_dim(sims, 0).length()
  let c1 = @metric.simplices_of_dim(sims, 1).length()
  let c2 = @metric.simplices_of_dim(sims, 2).length()
  let r1 = @core.rank_mod(b0, f)
  let r2 = @core.rank_mod(b1, f)
  let r3 = @core.rank_mod(b2, f)
  // 上同調：以轉置矩陣獨立求秩
  let d0 = @core.rank_mod(@core.mat_transpose(b0), f)
  let d1 = @core.rank_mod(@core.mat_transpose(b1), f)
  let d2 = @core.rank_mod(@core.mat_transpose(b2), f)
  let h0 = c0 - r1 - r2
  let h1 = c1 - r2 - r3
  let h2 = c2 - r3
  let ch0 = c0 - d1 - d0
  let ch1 = c1 - d2 - d1
  let ch2 = c2 - d2
  (dd, h0 == ch0 && h1 == ch1 && h2 == ch2)
}

///|
/// [T-Dual-Radon] Radon 變換的原像／餘核對偶：rank R = rank Rᵀ = n²（單射 ⟺ 滿射到 Rᵀ 的像）。
pub fn dual_radon_injectivity(
  n : Int32,
  p : Int32,
) -> (Bool, Bool, Int32, Int32) {
  let r = @radon.mk_radon(n, p)
  let m = @radon.radon_matrix(r)
  let f = @core.mk_field(p)
  let rk = @core.rank_mod(m, f)
  let rkt = @core.rank_mod(@core.mat_transpose(m), f)
  (rk == rkt, rk == n * n, rk, n * n)
}

///|
/// [T-Dual-Tensor] 張量指標置換對偶：2×2×2 超行列式在 6 個指標置換下不變。
pub fn dual_tensor_permutation(t : @tensor.Tensor3) -> Bool {
  let base = @tensor.hyperdet222(t)
  let mut ok = true
  for perm = 0; perm < 6; perm = perm + 1 {
    // 6 個置換的編碼：(i,j,k) → 依 perm 重排
    let q = @tensor.t3_of(2, 2, 2, t.field, (i, j, k) => {
      match perm {
        0 => @tensor.t3_get(t, i, j, k)
        1 => @tensor.t3_get(t, i, k, j)
        2 => @tensor.t3_get(t, j, i, k)
        3 => @tensor.t3_get(t, j, k, i)
        4 => @tensor.t3_get(t, k, i, j)
        _ => @tensor.t3_get(t, k, j, i)
      }
    })
    if @tensor.hyperdet222(q) != base {
      ok = false
    }
  }
  ok
}

// ---------------------------------------------------------------------------
// 3) 對比 contrast
// ---------------------------------------------------------------------------

///|
/// [D-Contrast] 兩族標籤的差集：(只在 A, 只在 B, 兩者皆是)。
pub fn contrast(
  a : Array[Bool],
  b : Array[Bool],
) -> (Array[Bool], Array[Bool], Array[Bool]) {
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  let only_a : Array[Bool] = Array::make(n, false)
  let only_b : Array[Bool] = Array::make(n, false)
  let both : Array[Bool] = Array::make(n, false)
  for i = 0; i < n; i = i + 1 {
    if a[i] && b[i] {
      both[i] = true
    } else if a[i] {
      only_a[i] = true
    } else if b[i] {
      only_b[i] = true
    }
  }
  (only_a, only_b, both)
}

///|
/// [T-Contrast-Partition] 對比的三塊只覆蓋 A ∪ B，且互不相交：
///   |onlyA| + |onlyB| + |both| = |A ∪ B|（本專案要求的「對比分割」恆等式）。
pub fn contrast_counts(
  a : Array[Bool],
  b : Array[Bool],
) -> (Int32, Int32, Int32) {
  let (oa, ob, bo) = contrast(a, b)
  let mut na = 0
  let mut nb = 0
  let mut nc = 0
  for i = 0; i < oa.length(); i = i + 1 {
    if oa[i] {
      na = na + 1
    }
    if ob[i] {
      nb = nb + 1
    }
    if bo[i] {
      nc = nc + 1
    }
  }
  (na, nb, nc)
}

///|
/// [T-Contrast-Partition] 檢查：三塊互斥、併集恰為 A ∪ B。
pub fn check_contrast_partition(a : Array[Bool], b : Array[Bool]) -> Bool {
  let (oa, ob, bo) = contrast(a, b)
  let mut ok = true
  let mut covered = 0
  let mut expect = 0
  for i = 0; i < oa.length(); i = i + 1 {
    let k = (if oa[i] { 1 } else { 0 }) +
      (if ob[i] { 1 } else { 0 }) +
      (if bo[i] { 1 } else { 0 })
    if k > 1 {
      ok = false // 互斥
    }
    covered = covered + k
    if a[i] || b[i] {
      expect = expect + 1
    }
  }
  ok && covered == expect
}

// ---------------------------------------------------------------------------
// 4) 蘊含 implication
// ---------------------------------------------------------------------------

///|
/// [D-Implies] 在有限樣本上「p ⟹ q」：不存在 p 真而 q 假的樣本。
pub fn implies(p : Array[Bool], q : Array[Bool]) -> Bool {
  let n = if p.length() < q.length() { p.length() } else { q.length() }
  let mut ok = true
  for i = 0; i < n; i = i + 1 {
    if p[i] && !q[i] {
      ok = false
    }
  }
  ok
}

///|
/// [E-ImplClosure] 蘊含矩陣的傳遞閉包（Floyd–Warshall 型）。
pub fn implication_closure(
  matrix : Array[Array[Bool]],
  n : Int32,
) -> Array[Array[Bool]] {
  let out : Array[Array[Bool]] = Array::makei(n, i => matrix[i].copy())
  for k = 0; k < n; k = k + 1 {
    for i = 0; i < n; i = i + 1 {
      for j = 0; j < n; j = j + 1 {
        if out[i][k] && out[k][j] {
          out[i][j] = true
        }
      }
    }
  }
  out
}

///|
/// [D-Predicates] 對 F₃ 的 6561 個 2×2×2 張量計算 5 個謂詞的真值表：
///   0: rank ≤ 1   1: Det = 0   2: rank-2 分解數 = 0（即 rank ≠ 2）   3: rank = 3   4: Det ≠ 0
///   （`classify222` 回傳的 `dc` 是 **rank-2** 分解數 —— 秩 1 與秩 3 都給 0，這正是
///   「秩 ≤ 1 ⟹ dc = 0」與「秩 = 3 ⟹ dc = 0」同時成立的原因。）
pub fn tensor_predicate_table() -> Array[Array[Bool]] {
  let tab = @tensor.rank1_table(2, 3)
  let cols : Array[Array[Bool]] = Array::makei(5, _ => [])
  for code = 0; code < @core.int_pow(3, 8); code = code + 1 {
    let mut c = code
    let t = @tensor.t3_make(2, 2, 2, 3)
    for i = 0; i < 8; i = i + 1 {
      t.data[i] = c % 3
      c = c / 3
    }
    let (rank, dc, det) = @tensor.classify222(t, tab)
    cols[0].push(rank <= 1)
    cols[1].push(det == 0)
    cols[2].push(dc == 0)
    cols[3].push(rank == 3)
    cols[4].push(det != 0)
  }
  cols
}

///|
/// [E-ImplMatrix] 由謂詞真值表算出蘊含矩陣（第 i 列 = 謂詞 i 蘊含謂詞 j）。
pub fn implication_matrix(table : Array[Array[Bool]]) -> Array[Array[Bool]] {
  let n = table.length()
  Array::makei(n, i => Array::makei(n, j => implies(table[i], table[j])))
}

///|
/// [T-Impl-Equiv] 雙向蘊含 = 等價；回傳所有等價對 (i, j)（i < j）。
pub fn equivalences(closure : Array[Array[Bool]]) -> Array[(Int32, Int32)] {
  let out : Array[(Int32, Int32)] = []
  let n = closure.length()
  for i = 0; i < n; i = i + 1 {
    for j = i + 1; j < n; j = j + 1 {
      if closure[i][j] && closure[j][i] {
        out.push((i, j))
      }
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 5) 比率 ratio
// ---------------------------------------------------------------------------

///|
/// [D-Ratio] 比值約分（分子/分母；分母 0 時回傳 (0, 1)）。
pub fn ratio(a : Int32, b : Int32) -> (Int32, Int32) {
  if b == 0 {
    return (0, 1)
  }
  let g = @core.igcd(a, b)
  if g == 0 {
    (0, 1)
  } else {
    (a / g, b / g)
  }
}

///|
/// [E-ConstantRatio] 一族比值全部相等時回傳該值（約分後），否則 None。
pub fn constant_ratio(pairs : Array[(Int32, Int32)]) -> (Int32, Int32)? {
  if pairs.length() == 0 {
    return None
  }
  let first = ratio(pairs[0].0, pairs[0].1)
  let mut ok = true
  for pair in pairs {
    if ratio(pair.0, pair.1) != first {
      ok = false
    }
  }
  if ok {
    Some(first)
  } else {
    None
  }
}

///|
/// [T-Ratio-Radon] Σ_lines (Rf) / Σ_x f = n+1 ——「總質量守恆」的**比率**形式。
///   在 F_p 中取比值（先約化再相除），故不受整體尺度與模約化的影響；
///   Σf ≡ 0 時比值不存在，回傳 None（這是定理的必要前提，而不是特例）。
pub fn radon_total_relative(n : Int32, p : Int32, f : Array[Int32]) -> Int32? {
  let r = @radon.mk_radon(n, p)
  let m = @radon.radon_matrix(r)
  let mf = @core.mat_mul_vec(m, f, p)
  let fld = @core.mk_field(p)
  let mut s1 = 0
  for x in mf {
    s1 = @core.fld_add(fld, s1, x)
  }
  let mut s0 = 0
  for x in f {
    s0 = @core.fld_add(fld, s0, x)
  }
  if s0 == 0 {
    None
  } else {
    Some(relative(s1, s0, p))
  }
}

///|
/// [T-Ratio-Flip] 翻轉圖 k-正則 ⟹ #edges : #vertices = k : 2 = (n−3) : 2。
pub fn flip_edge_vertex_ratio(n : Int32) -> (Int32, Int32) {
  let tris = @nc.triangulations(n)
  let k = @nc.flip_degrees(tris)[0]
  let v = tris.length()
  ratio(v * k, 2 * v)
}

///|
/// [E-Collect] 把五類關係的計算結果全部收成記錄列（可直接灌入持久賬本）。
pub fn collect(n_radon : Int32, p : Int32) -> Array[Rec] {
  let out : Array[Rec] = []
  // 相對：尺度不變
  out.push(rec(0, 1, 0, check_relative_scale_invariance([3, 6, 9, 12], 5, p)))
  // 對偶：rank/空度、Radon 的單射性
  let m = @core.mat_from_rows([[1, 2, 3], [4, 5, 6], [7, 8, 10]])
  out.push(rec(1, 0, 0, dual_rank_nullity(m, p)))
  let (dr, inj, _rk, _nc) = dual_radon_injectivity(n_radon, p)
  out.push(rec(1, 1, 0, dr && inj))
  // 比率：Radon 的總質量比
  let f = Array::makei(n_radon * n_radon, i => (i * 7 + 1) % p)
  let rel = radon_total_relative(n_radon, p, f)
  let ok_ratio = match rel {
    Some(v) => v == n_radon + 1
    None => false
  }
  out.push(rec(4, n_radon + 1, 1, ok_ratio))
  out
}

///|
/// [E-CollectInto] 把收集到的五類關係寫進**持久賬本**（每個關係一條記錄，可稽核、可重放）。
///   回傳 (新賬本, 寫入條數)。
pub fn collect_into_ledger(
  l : @ledger.Ledger,
  n_radon : Int32,
  p : Int32,
) -> (@ledger.Ledger, Int32) {
  let recs = collect(n_radon, p)
  let mut out = l
  let mut cnt = 0
  for r in recs {
    out = @ledger.append(out, 2, rec_values(r), [])
    cnt = cnt + 1
  }
  (out, cnt)
}
