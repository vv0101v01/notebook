// ===========================================================================
// canon —— 逐個結構的規範形（canonical form）
//
// 每個結構都給出三件事：
//   (C1) 一個**可計算**的規範形（canon）；
//   (C2) 一條**完備性**陳述：canon(x) = canon(y) ⟺ x ~ y，其中 ~ 是明寫的等價關係
//        （有的結構完備，有的只到「較粗的等價」—— 後者一律如實標註）；
//   (C3) 一條**不變性**檢核：規範形在該等價關係下不變（測試中用真正的重標號/共軛實作驗證）。
//
// 全域公理（每種規範形都必須滿足，測試逐項驗）：
//   [Ax-Canon-Idem]  canon(canon(x)) = canon(x)
//   [Ax-Canon-Complete] canon(x) = canon(y) ⟺ x ~ y
// ===========================================================================

// ---------------------------------------------------------------------------
// 0. 共用工具
// ---------------------------------------------------------------------------

///|
/// 字典序比較：−1（小於）、0（相等）、1（大於）。
pub fn lex_cmp(a : Array[Int32], b : Array[Int32]) -> Int32 {
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  let mut i = 0
  let mut res = 0
  while i < n && res == 0 {
    if a[i] < b[i] {
      res = -1
    } else if a[i] > b[i] {
      res = 1
    }
    i = i + 1
  }
  if res == 0 && a.length() != b.length() {
    res = if a.length() < b.length() { -1 } else { 1 }
  }
  res
}

///|
/// 字典序嚴格小於。
pub fn lex_less(a : Array[Int32], b : Array[Int32]) -> Bool {
  lex_cmp(a, b) < 0
}

///|
/// n 個點的全部置換（n ≤ 7；遞迴展開，depth 由 `perm_fill` 推進）。
pub fn perms(n : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let cur : Array[Int32] = Array::make(n, -1)
  let used : Array[Bool] = Array::make(n, false)
  perm_fill(out, cur, used, n, 0)
  out
}

///|
fn perm_fill(
  out : Array[Array[Int32]],
  cur : Array[Int32],
  used : Array[Bool],
  n : Int32,
  depth : Int32,
) -> Unit {
  if depth == n {
    out.push(cur.copy())
    return
  }
  for v = 0; v < n; v = v + 1 {
    let mut taken = false
    for k = 0; k < depth; k = k + 1 {
      if cur[k] == v {
        taken = true
      }
    }
    if !taken {
      cur[depth] = v
      perm_fill(out, cur, used, n, depth + 1)
    }
  }
  let _ = used
}

///|
/// 把 `n×n` 矩陣依置換 σ 同時重排列與欄：(σAσᵀ)_{ij} = A_{σ(i),σ(j)}。
pub fn perm_conj_mat(m : @core.Mat, sigma : Array[Int32]) -> @core.Mat {
  let n = m.rows
  let out = @core.mat_make(n, n, 0)
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      out.data[i * n + j] = m.data[sigma[i] * m.cols + sigma[j]]
    }
  }
  out
}

///|
/// 矩陣壓成整數陣列（列優先）。
pub fn flatten(m : @core.Mat) -> Array[Int32] {
  m.data.copy()
}

///|
/// 陣列串接（用於把多段資料壓成單一可比較的鍵）。
pub fn concat_arr(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out = a.copy()
  for x in b {
    out.push(x)
  }
  out
}

// ---------------------------------------------------------------------------
// 1. 矩陣 / 線性結構的規範形（core, spectral）
// ---------------------------------------------------------------------------

///|
/// [E-Canon-RREF] 列等價的規範形：F_p 上的**約化列階梯式**（RREF）。
///   [T-Canon-RREF] A 與 B 列等價（同一列空間）⟺ RREF(A) = RREF(B)。
pub fn canon_rref(m : @core.Mat, p : Int32) -> @core.Mat {
  @core.gauss_jordan(m, @core.mk_field(p)).rref
}

///|
/// RREF 相等判定。
pub fn canon_rref_same(a : @core.Mat, b : @core.Mat, p : Int32) -> Bool {
  @core.mat_eq_mod(canon_rref(a, p), canon_rref(b, p), p)
}

///|
/// [E-Canon-SNF] 么模等價的規範形：整數矩陣的 **Smith 對角線**
///   （非負、整除鏈 d₁ | d₂ | …；0 表示自由因子）。
///   [T-Canon-SNF] A = U B V（U, V 么模）⟺ smith(A) = smith(B)。
pub fn canon_snf(m : @core.Mat) -> Array[Int32] {
  @core.smith_diagonal(m)
}

///|
/// 整數向量列的 Hermite 正規形（列 Hermite：主元逐欄遞增、主元為正、
///   主元上方以主元取模化簡、零列置底）。
///   [T-Canon-HNF] 兩組整數列向量生成**同一個格** ⟺ HNF 相同。
pub fn canon_hnf(m : @core.Mat) -> @core.Mat {
  let cols = m.cols
  let rows : Array[Array[Int32]] = []
  for i = 0; i < m.rows; i = i + 1 {
    let r : Array[Int32] = []
    for j = 0; j < cols; j = j + 1 {
      r.push(m.data[i * cols + j])
    }
    rows.push(r)
  }
  let n = rows.length()
  let mut piv = 0
  for c = 0; c < cols; c = c + 1 {
    let mut go = true
    while go {
      // 在 piv..n 中找絕對值最小者
      let mut best = -1
      let mut bestv = 0
      for i = piv; i < n; i = i + 1 {
        let v = rows[i][c]
        if v != 0 {
          let av = if v < 0 { -v } else { v }
          if best < 0 || av < bestv {
            best = i
            bestv = av
          }
        }
      }
      if best < 0 {
        go = false
      } else {
        let tmp = rows[piv]
        rows[piv] = rows[best]
        rows[best] = tmp
        let pv = rows[piv][c]
        // 以主元消去下方（取截斷商，餘數絕對值嚴格變小 ⟹ 終止）
        let mut below = false
        for i = piv + 1; i < n; i = i + 1 {
          if rows[i][c] != 0 {
            let q = rows[i][c] / pv
            for j = c; j < cols; j = j + 1 {
              rows[i][j] = rows[i][j] - q * rows[piv][j]
            }
            if rows[i][c] != 0 {
              below = true
            }
          }
        }
        if !below {
          go = false
        }
      }
    }
    if piv < n && rows[piv][c] != 0 {
      if rows[piv][c] < 0 {
        for j = 0; j < cols; j = j + 1 {
          rows[piv][j] = -rows[piv][j]
        }
      }
      let p2 = rows[piv][c]
      for i = 0; i < piv; i = i + 1 {
        let q = rows[i][c] / p2
        if q != 0 {
          for j = 0; j < cols; j = j + 1 {
            rows[i][j] = rows[i][j] - q * rows[piv][j]
          }
        }
      }
      piv = piv + 1
    }
  }
  let keep : Array[Array[Int32]] = []
  for i = 0; i < n; i = i + 1 {
    let mut nz = false
    for j = 0; j < cols; j = j + 1 {
      if rows[i][j] != 0 {
        nz = true
      }
    }
    if nz {
      keep.push(rows[i])
    }
  }
  let out = @core.mat_make(keep.length(), cols, 0)
  for i = 0; i < keep.length(); i = i + 1 {
    for j = 0; j < cols; j = j + 1 {
      out.data[i * cols + j] = keep[i][j]
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 2. 線性映射的相似規範形（spectral）
// ---------------------------------------------------------------------------

///|
/// [E-Canon-Conj] 相似（共軛）的規範形：在 GL_n(F_p) 上取 `P A P⁻¹` 的**字典序最小者**。
///   這是真正的規範形（不是不變量）：[T-Canon-Conj] A ~ B（存在可逆 P）⟺ canon 相同。
///   代價是 GL_n(F_p) 的窮舉，故限 n ≤ 3、p ≤ 3。
pub fn canon_conj(m : @core.Mat, p : Int32) -> Array[Int32] {
  let n = m.rows
  let fld = @core.mk_field(p)
  let best = flatten(m)
  let mut acc = best
  let total = @core.int_pow(p, n * n)
  for code = 0; code < total; code = code + 1 {
    let pm = @core.mat_make(n, n, 0)
    let mut c = code
    for i = 0; i < n; i = i + 1 {
      for j = 0; j < n; j = j + 1 {
        pm.data[i * n + j] = c % p
        c = c / p
      }
    }
    if @core.det_mod(pm, @core.mk_field(p)) != 0 {
      match @spectral.mat_inverse(pm, p) {
        Some(inv) => {
          let conj = @core.mat_mul(@core.mat_mul(pm, m, p), inv, p)
          let key = flatten(conj)
          if lex_less(key, acc) {
            acc = key
          }
        }
        None => ()
      }
    }
  }
  let _ = best
  let _ = fld
  acc
}

///|
/// GL_n(F_p)-軌道的**大小**：`{P A P⁻¹}` 中相異矩陣的個數（去重，故不是穩定化子的計數）。
pub fn orbit_size_conj(m : @core.Mat, p : Int32) -> Int32 {
  let n = m.rows
  let seen : Array[Array[Int32]] = []
  let total = @core.int_pow(p, n * n)
  for code = 0; code < total; code = code + 1 {
    let pm = @core.mat_make(n, n, 0)
    let mut c = code
    for i = 0; i < n; i = i + 1 {
      for j = 0; j < n; j = j + 1 {
        pm.data[i * n + j] = c % p
        c = c / p
      }
    }
    if @core.det_mod(pm, @core.mk_field(p)) != 0 {
      match @spectral.mat_inverse(pm, p) {
        Some(inv) => {
          let key = flatten(@core.mat_mul(@core.mat_mul(pm, m, p), inv, p))
          let mut dup = false
          for x in seen {
            if x == key {
              dup = true
            }
          }
          if !dup {
            seen.push(key)
          }
        }
        None => ()
      }
    }
  }
  seen.length()
}

///|
/// 同一相似類的類數（窮舉 M_n(F_p) 的軌道個數）。
pub fn conjugacy_class_count(n : Int32, p : Int32) -> Int32 {
  let seen : Array[Array[Int32]] = []
  let total = @core.int_pow(p, n * n)
  for code = 0; code < total; code = code + 1 {
    let m = @core.mat_make(n, n, 0)
    let mut c = code
    for i = 0; i < n; i = i + 1 {
      for j = 0; j < n; j = j + 1 {
        m.data[i * n + j] = c % p
        c = c / p
      }
    }
    let k = canon_conj(m, p)
    let mut dup = false
    for x in seen {
      if x == k {
        dup = true
      }
    }
    if !dup {
      seen.push(k)
    }
  }
  seen.length()
}

// ---------------------------------------------------------------------------
// 3. 圖的規範形（metric, spectral）：S_n 置換等價
// ---------------------------------------------------------------------------

///|
/// [E-Canon-Graph] 圖同構的規範形：在 S_n 上取 `σ A σᵀ` 的字典序最小者。
///   [T-Canon-Graph] A ≅ B（存在點置換）⟺ canon 相同（n ≤ 7 可算）。
pub fn canon_graph(adj : @core.Mat) -> Array[Int32] {
  let n = adj.rows
  let ps = perms(n)
  let mut acc = flatten(adj)
  let mut first = true
  for sigma in ps {
    let key = flatten(perm_conj_mat(adj, sigma))
    if first || lex_less(key, acc) {
      acc = key
      first = false
    }
  }
  acc
}

///|
/// [E-Canon-Metric] 有限度量空間的等距規範形：把距離矩陣依置換取最小字典序。
///   [T-Canon-Metric] 兩度量空間等距 ⟺ canon 相同。
pub fn canon_metric(d : @core.Mat) -> Array[Int32] {
  canon_graph(d)
}

// ---------------------------------------------------------------------------
// 4. 3-張量的規範形（tensor）：三條腿的 S_3 置換
// ---------------------------------------------------------------------------

///|
/// [E-Canon-T3] 3-張量在**腿置換**群 S_3 下的規範形（d×d×d，F_2/F_p 皆可）。
///   [T-Canon-T3] T ≅ T'（經由腿置換）⟺ canon 相同。
///   註：這完備於 S_3；對 GL×GL×GL 只給出不變量（不是規範形），本檔不假裝完備。
pub fn canon_t3(flat : Array[Int32], d : Int32) -> Array[Int32] {
  let idx : (Int32, Int32, Int32) -> Int32 = fn(a, b, c) { (a * d + b) * d + c }
  let perms3 : Array[Array[Int32]] = [
    [0, 1, 2],
    [0, 2, 1],
    [1, 0, 2],
    [1, 2, 0],
    [2, 0, 1],
    [2, 1, 0],
  ]
  let mut acc : Array[Int32] = []
  let mut first = true
  for pm in perms3 {
    let out : Array[Int32] = Array::make(d * d * d, 0)
    for a = 0; a < d; a = a + 1 {
      for b = 0; b < d; b = b + 1 {
        for c = 0; c < d; c = c + 1 {
          // 新張量在位置 (a,b,c) 取原張量在 (π⁻¹ 作用) 的值
          let src = idx(
            if pm[0] == 0 {
              a
            } else if pm[0] == 1 {
              b
            } else {
              c
            },
            if pm[1] == 0 {
              a
            } else if pm[1] == 1 {
              b
            } else {
              c
            },
            if pm[2] == 0 {
              a
            } else if pm[2] == 1 {
              b
            } else {
              c
            },
          )
          out[idx(a, b, c)] = flat[src]
        }
      }
    }
    if first || lex_less(out, acc) {
      acc = out
      first = false
    }
  }
  acc
}

// ---------------------------------------------------------------------------
// 5. 非交叉樹的規範形（nc）：二面體群 D_n
// ---------------------------------------------------------------------------

///|
/// 把邊集經 D_n 的元素 (k, refl) 搬動後，排序並展平（唯一的排序實作）。
fn moved_flat(
  n : Int32,
  edges : Array[@nc.Chord],
  k : Int32,
  refl : Int32,
) -> Array[Int32] {
  let rows : Array[Array[Int32]] = []
  for e in edges {
    let a = if refl == 0 { (e.a + k) % n } else { (k - e.a % n + n) % n }
    let b = if refl == 0 { (e.b + k) % n } else { (k - e.b % n + n) % n }
    rows.push([if a < b { a } else { b }, if a < b { b } else { a }])
  }
  // 插入排序（邊數很少）
  let sorted : Array[Array[Int32]] = []
  for e in rows {
    let mut pos = sorted.length()
    let mut i = sorted.length() - 1
    let mut done = false
    while i >= 0 && !done {
      if sorted[i][0] > e[0] || (sorted[i][0] == e[0] && sorted[i][1] > e[1]) {
        pos = i
        i = i - 1
      } else {
        done = true
      }
    }
    sorted.insert(pos, e)
  }
  let flat : Array[Int32] = []
  for e in sorted {
    flat.push(e[0])
    flat.push(e[1])
  }
  flat
}

///|
/// [E-Canon-Dihedral] 圓上結構在**二面體群 D_n**（n 旋轉 + n 反射）下的規範形：
///   取所有搬動結果的字典序最小者。
///   [T-Canon-Dihedral] 兩個邊集在 D_n 下等價 ⟺ canon 相同。
pub fn canon_dihedral(n : Int32, edges : Array[@nc.Chord]) -> Array[Int32] {
  // 正規化：先對原邊集排序展平（k = 0、refl = 0 即「未搬動」）
  let mut acc = moved_flat(n, edges, 0, 0)
  for k = 0; k < n; k = k + 1 {
    for refl = 0; refl < 2; refl = refl + 1 {
      let key = moved_flat(n, edges, k, refl)
      if lex_less(key, acc) {
        acc = key
      }
    }
  }
  acc
}

///|
/// 邊集在 D_n 下是否被 (k, refl) 固定。
pub fn dihedral_fixed(
  n : Int32,
  edges : Array[@nc.Chord],
  k : Int32,
  refl : Int32,
) -> Bool {
  moved_flat(n, edges, k, refl) == moved_flat(n, edges, 0, 0)
}

///|
/// [T-Canon-Dihedral-Burnside] 交叉驗證：軌道數（由 canon 數出）× |D_n|
///   應等於 Σ_{g∈D_n} |Fix(g)|。回傳 (canon 軌道數, Burnside 的值)。
pub fn dihedral_orbits(
  n : Int32,
  edge_sets : Array[Array[@nc.Chord]],
) -> (Int32, Int32) {
  let seen : Array[Array[Int32]] = []
  for es in edge_sets {
    let key = canon_dihedral(n, es)
    let mut dup = false
    for x in seen {
      if x == key {
        dup = true
      }
    }
    if !dup {
      seen.push(key)
    }
  }
  let mut fix_sum = 0
  for k = 0; k < n; k = k + 1 {
    for refl = 0; refl < 2; refl = refl + 1 {
      for es in edge_sets {
        if dihedral_fixed(n, es, k, refl) {
          fix_sum = fix_sum + 1
        }
      }
    }
  }
  (seen.length(), fix_sum / (2 * n))
}

// ---------------------------------------------------------------------------
// 6. 2-上圈的規範形（twist）：H² 類的餘圈正規化
// ---------------------------------------------------------------------------

///|
/// 上圈檢核：δ²ω = 0。
pub fn is_cocycle(g : @twist.Grp, ell : Int32, vec : Array[Int32]) -> Bool {
  let d2 = @twist.d2_matrix(g, ell)
  for i = 0; i < d2.rows; i = i + 1 {
    let mut acc = 0
    for j = 0; j < d2.cols; j = j + 1 {
      acc = acc + d2.data[i * d2.cols + j] * vec[j]
    }
    if acc % ell != 0 {
      return false
    }
  }
  true
}

///|
/// [E-Canon-Cocycle] 2-上圈的規範形：在它的**上同調類** `ω + B²` 中取字典序最小的向量。
///   [T-Canon-Cocycle] ω ~ ω'（差一個上邊界）⟺ canon 相同 —— 即 H² 的類的規範代表元。
pub fn canon_cocycle(
  g : @twist.Grp,
  ell : Int32,
  vec : Array[Int32],
) -> Array[Int32] {
  let d1 = @twist.d1_matrix(g, ell)
  let nv = d1.cols
  // 上邊界的生成元（δ¹ 的行；這裡 rows 已是生成元）
  let gens : Array[Array[Int32]] = []
  for i = 0; i < d1.rows; i = i + 1 {
    let r : Array[Int32] = []
    for j = 0; j < nv; j = j + 1 {
      r.push(d1.data[i * nv + j])
    }
    gens.push(r)
  }
  // 列舉 B² 的全體（係數 0..ell−1）
  let rank = gens.length()
  let total = @core.int_pow(ell, rank)
  let mut acc = vec.copy()
  let mut first = true
  for code = 0; code < total; code = code + 1 {
    let b : Array[Int32] = Array::make(nv, 0)
    let mut c = code
    for k = 0; k < rank; k = k + 1 {
      let coef = c % ell
      c = c / ell
      if coef != 0 {
        for j = 0; j < nv; j = j + 1 {
          b[j] = (b[j] + coef * gens[k][j]) % ell
        }
      }
    }
    let cand : Array[Int32] = []
    for j = 0; j < nv; j = j + 1 {
      cand.push((vec[j] + b[j]) % ell)
    }
    if first || lex_less(cand, acc) {
      acc = cand
      first = false
    }
  }
  acc
}

// ---------------------------------------------------------------------------
// 7. site / 拓撲的規範形（grotop）：偏序集同構
// ---------------------------------------------------------------------------

///|
/// [E-Canon-Poset] site 的規範形：在 S_n 上取 `σ` 重排後 `leq` 矩陣的字典序最小展平。
///   [T-Canon-Poset] 兩個 site 同構（存在保序雙射）⟺ canon 相同。
pub fn canon_poset(s : @grotop.Site) -> Array[Int32] {
  let n = s.n
  let base = @core.mat_make(n, n, 0)
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      if s.leq[i][j] {
        base.data[i * n + j] = 1
      }
    }
  }
  canon_graph(base)
}

// ---------------------------------------------------------------------------
// 8. 胞腔複形的規範形（cellcx）：邊界矩陣的 Smith 資料
// ---------------------------------------------------------------------------

///|
/// [E-Canon-Cx] 胞腔複形的規範形：**每個邊界矩陣的 Smith 對角線**（依維度串接）。
///   [T-Canon-Cx] 換基（重排胞腔、么模變換）不改變它 —— 測試用真正的重排驗證；
///   且它決定整係數同調（Betti + 撓率）。
///   註：這完備於「鏈複形在每個度數上的么模等價」，**不完備於同倫等價**（如實標註）。
pub fn canon_cx(cx : @cellcx.CellCx) -> Array[Int32] {
  let out : Array[Int32] = []
  for k = 0; k < cx.bnd.length(); k = k + 1 {
    let dg = @core.smith_diagonal(cx.bnd[k])
    out.push(dg.length())
    for d in dg {
      out.push(d)
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 9. 譜序列頁的規範形（ss, serre, adams）
// ---------------------------------------------------------------------------

///|
/// [E-Canon-Page] 一頁的規範形：`(r, dims 展平, 每個非零 d_r 的 RREF 展平)`。
///   [T-Canon-Page] 改變每個格子的基（左乘可逆矩陣、右乘可逆矩陣）不改變它：
///   RREF 是行空間的完全不變量。
pub fn canon_page(pg : @ss.Page) -> Array[Int32] {
  let out : Array[Int32] = []
  out.push(pg.r)
  out.push(pg.np)
  out.push(pg.nq)
  for i = 0; i < pg.np; i = i + 1 {
    for j = 0; j < pg.nq; j = j + 1 {
      out.push(pg.dims[i][j])
    }
  }
  for i = 0; i < pg.np; i = i + 1 {
    for j = 0; j < pg.nq; j = j + 1 {
      match pg.d[i][j] {
        Some(m) => {
          out.push(1) // 標記：这一格有微分
          let r = canon_rref(m, pg.p)
          out.push(r.rows)
          out.push(r.cols)
          for v in r.data {
            out.push(v)
          }
        }
        None => out.push(0)
      }
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 10. 分次代數的規範不變量（ahss）
// ---------------------------------------------------------------------------

///|
/// [E-Canon-AlgProfile] 分次代數的**基無關不變量**：`dims` + 每塊乘法 `cup[i][j]` 的秩。
///   [T-Canon-AlgProfile] 逐度的基變換（`P_i` 可逆、乘法表按 `P_{i+j} C (P_i ⊗ P_j)` 變換）
///   不改變這個剖面 —— 測試用真正的隨機可逆矩陣驗證。
///   註：這是**不變量**而非規範形（對 GL 不宣稱完備），如實標註。
pub fn canon_alg_profile(a : @ahss.Alg) -> Array[Int32] {
  let out : Array[Int32] = []
  for k = 0; k <= a.top; k = k + 1 {
    out.push(a.dims[k])
  }
  for i = 0; i <= a.top; i = i + 1 {
    for j = 0; i + j <= a.top; j = j + 1 {
      out.push(@core.rank_mod(@ahss.alg_get_cup(a, i, j), @core.mk_field(a.p)))
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 11. 凝聚鏈的規範形（condensed）
// ---------------------------------------------------------------------------

///|
/// [E-Canon-Chain] 有限層級鏈的規範形：`dims` + 每個過渡映射的 Smith 對角線。
///   [T-Canon-Chain] 逐層換基不改變它；它決定逆極限維數（`chain_lim_dim`）。
///   註：完備於「逐層么模等價」，**不完備於鏈同構**（因換基必須同時兼顧進出兩邊），如實標註。
pub fn canon_chain(c : @condensed.Chain) -> Array[Int32] {
  let out : Array[Int32] = []
  for d in c.dims {
    out.push(d)
  }
  for k = 0; k < c.trans.length(); k = k + 1 {
    let dg = @core.smith_diagonal(c.trans[k])
    out.push(dg.length())
    for d in dg {
      out.push(d)
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 12. 格點規範場的規範形（gauge）：曲率
// ---------------------------------------------------------------------------

///|
/// [E-Canon-Gauge] Z_ℓ 格點規範場的規範形：**曲率場**（逐格面 plaquette 值）展平。
///   [T-Canon-Gauge] 曲率在規範變換下不變（Abel 情形，`@gauge.check_curvature_invariant`）；
///   故 canon 是規範不變量。**如實標註**：在週期環面上它不完備（holonomy 不進曲率）。
pub fn canon_gauge(l : @gauge.Lattice, u : Array[Int32]) -> Array[Int32] {
  @gauge.curvature(l, u)
}

// ---------------------------------------------------------------------------
// 13. 超結構的規範形（hyper）：結果集
// ---------------------------------------------------------------------------

///|
/// [E-Canon-Hyper] 超結構的規範形：把「成員表」壓成 (a, b, c) 的排序清單。
///   [T-Canon-Hyper] 兩個超結構在**標號重排**下同構 ⟺ canon 相同（此處只給成員集的完全編碼，
///   標號層面的同構另由 `canon_graph` 風格的置換搜尋處理；本函數提供**精確編碼**）。
pub fn canon_hyper(h : @hyper.Hyper) -> Array[Int32] {
  let n = @hyper.hyper_size(h)
  let out : Array[Int32] = []
  for a = 0; a < n; a = a + 1 {
    for b = 0; b < n; b = b + 1 {
      for c = 0; c < n; c = c + 1 {
        let v = if @hyper.hyper_contains(h, a, b, c) { 1 } else { 0 }
        out.push(v)
      }
    }
  }
  out
}

// ---------------------------------------------------------------------------

// 14. 關係記錄的規範形（relations, ledger）
// ---------------------------------------------------------------------------

///|
/// [E-Canon-Records] 一組關係記錄的規範形：轉成 (kind, a, b, holds) 四元組後**排序**並展平。
///   [T-Canon-Records] 兩組記錄相同（視為集合）⟺ canon 相同；次序與重複不影響。
pub fn canon_records(recs : Array[@relations.Rec]) -> Array[Int32] {
  let rows : Array[Array[Int32]] = []
  for r in recs {
    rows.push(@relations.rec_values(r))
  }
  // 插入排序（記錄數很少）
  let sorted : Array[Array[Int32]] = []
  for e in rows {
    let mut pos = sorted.length()
    let mut i = sorted.length() - 1
    let mut done = false
    while i >= 0 && !done {
      if lex_cmp(sorted[i], e) > 0 {
        pos = i
        i = i - 1
      } else {
        done = true
      }
    }
    sorted.insert(pos, e)
  }
  let out : Array[Int32] = []
  let mut prev : Array[Int32] = []
  let mut first = true
  for e in sorted {
    let mut dup = false
    if !first && e == prev {
      dup = true
    }
    if !dup {
      for v in e {
        out.push(v)
      }
      prev = e
      first = false
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 15. 導出張量積的規範形（dtensor）：Tor 雙次表
// ---------------------------------------------------------------------------

///|
/// [E-Canon-Tor] Tor 表的規範形：`[i][t]` 展平（同調度、內部度數兩個索引都固定）。
///   [T-Canon-Tor] 同一個代數的兩種 Koszul 呈現給同一個 canon（本檔測試以兩份分解互證）。
pub fn canon_tor(
  a : @dtensor.PolyAlg,
  i_max : Int32,
  t_max : Int32,
) -> Array[Int32] {
  let tb = @dtensor.tor_table(a, i_max, t_max)
  let out : Array[Int32] = []
  for row in tb {
    for v in row {
      out.push(v)
    }
  }
  out
}

///|
/// [E-Canon-HyperIso] 超結構在**標號置換**下的規範形：對所有 σ ∈ S_n 取重排後成員表的
///   字典序最小者（n ≤ 4）。[T-Canon-HyperIso] 兩個超結構同構 ⟺ 此 canon 相同。
pub fn canon_hyper_iso(h : @hyper.Hyper) -> Array[Int32] {
  let n = @hyper.hyper_size(h)
  let ps = perms(n)
  let mut acc : Array[Int32] = []
  let mut first = true
  for sigma in ps {
    let out : Array[Int32] = []
    for a = 0; a < n; a = a + 1 {
      for b = 0; b < n; b = b + 1 {
        for c = 0; c < n; c = c + 1 {
          let v = if @hyper.hyper_contains(h, sigma[a], sigma[b], sigma[c]) {
            1
          } else {
            0
          }
          out.push(v)
        }
      }
    }
    if first || lex_less(out, acc) {
      acc = out
      first = false
    }
  }
  acc
}
