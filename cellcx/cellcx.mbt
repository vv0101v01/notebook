// ============================================================================
// @tensorlab/cellcx —— 有限胞腔複形、整係數同調、胞腔積、持續同調（條碼）
// ----------------------------------------------------------------------------
// 本檔定理／算法：
//   [D-CellCx]   有限 CW 複形 = 每維胞腔數 + 邊界矩陣 ∂_k : C_k → C_{k−1}
//   [T-Cell-DD]  ∂_{k−1}∘∂_k = 0（每個建構子都回報這個檢查）
//   [T-Cell-Betti]   β_k = #(k-胞腔) − rank ∂_k − rank ∂_{k+1}
//   [T-Cell-Euler]   χ = Σ(−1)^k #cells = Σ(−1)^k β_k
//   [E-IntHom]   整係數同調：Smith 標準形給出自由秩 + 撓（Z/k）
//   [D-Leibniz]  胞腔積：(a×b) 的邊界 = ∂a×b + (−1)^{|a|} a×∂b
//   [E-Persist]  持續同調 = 依過濾序化簡邊界矩陣（標準算法），輸出條碼 (dim,birth,death)
//   [T-Persist-Betti]  持續 Betti 數 = 區間覆蓋函數
//   [E-Simplicial]  由單純形列表建胞腔複形（含定向符號），閉包自動補齊
// ============================================================================

///|
/// [D-CellCx] 有限胞腔複形。`bnd[k]` 是 ∂_{k+1} : C_{k+1} → C_k（大小 counts[k] × counts[k+1]），
/// 故 `bnd` 的長度 = dims；`p` 為同調用的質數（整係數同調不看它）。
pub struct CellCx {
  dims : Int32
  counts : Array[Int32]
  bnd : Array[@core.Mat]
  p : Int32
}

///|
pub fn cx_new(
  counts : Array[Int32],
  bnd : Array[@core.Mat],
  p : Int32,
) -> CellCx {
  CellCx::{ dims: counts.length() - 1, counts, bnd, p, }
}

///|
pub fn cx_cell_count(cx : CellCx, k : Int32) -> Int32 {
  if k < 0 || k > cx.dims {
    0
  } else {
    cx.counts[k]
  }
}

///|
pub fn cx_top_dim(cx : CellCx) -> Int32 {
  cx.dims
}

///|
pub fn cx_field(cx : CellCx) -> Int32 {
  cx.p
}

///|
/// [T-Cell-DD] 邊界平方為零。
pub fn cx_check_dd(cx : CellCx) -> Bool {
  let f = @core.mk_field(cx.p)
  let mut ok = true
  for k = 1; k < cx.dims; k = k + 1 {
    let comp = @core.mat_mul(cx.bnd[k - 1], cx.bnd[k], cx.p)
    let _ = f
    if !@core.mat_is_zero(comp) {
      ok = false
    }
  }
  ok
}

///|
/// rank ∂_k（∂_0 = 0）。
pub fn cx_rank_bnd(cx : CellCx, k : Int32) -> Int32 {
  if k <= 0 || k > cx.dims {
    0
  } else {
    @core.rank_mod(cx.bnd[k - 1], @core.mk_field(cx.p))
  }
}

///|
/// rank ∂_k 的整數版本（Smith 標準形非零項數）。
pub fn cx_rank_int(cx : CellCx, k : Int32) -> Int32 {
  if k <= 0 || k > cx.dims {
    0
  } else {
    let dg = @core.smith_diagonal(cx.bnd[k - 1])
    let mut r = 0
    for d in dg {
      if d != 0 {
        r = r + 1
      }
    }
    r
  }
}

///|
/// [T-Cell-Betti] β_k = c_k − rank ∂_k − rank ∂_{k+1}（F_p 係數）。
pub fn cx_betti(cx : CellCx, k : Int32) -> Int32 {
  cx_cell_count(cx, k) - cx_rank_bnd(cx, k) - cx_rank_bnd(cx, k + 1)
}

///|
pub fn cx_betti_all(cx : CellCx) -> Array[Int32] {
  Array::makei(cx.dims + 1, k => cx_betti(cx, k))
}

///|
/// [T-Cell-Euler] χ = Σ(−1)^k c_k。
pub fn cx_euler(cx : CellCx) -> Int32 {
  let mut s = 0
  let mut sgn = 1
  for k = 0; k <= cx.dims; k = k + 1 {
    s = s + sgn * cx.counts[k]
    sgn = -sgn
  }
  s
}

///|
/// [T-Cell-Euler] χ = Σ(−1)^k β_k（與胞腔計數的一致性檢查）。
pub fn cx_euler_betti(cx : CellCx) -> Int32 {
  let mut s = 0
  let mut sgn = 1
  for k = 0; k <= cx.dims; k = k + 1 {
    s = s + sgn * cx_betti(cx, k)
    sgn = -sgn
  }
  s
}

///|
/// [T-Cell-Sphere] 同調是否為 S^n 的（β_0 = β_n = 1，其餘 0）。
pub fn cx_is_sphere(cx : CellCx, n : Int32) -> Bool {
  let bs = cx_betti_all(cx)
  let mut ok = bs.length() == n + 1
  for k = 0; k < bs.length(); k = k + 1 {
    let want = if k == 0 || k == n { 1 } else { 0 }
    if bs[k] != want {
      ok = false
    }
  }
  ok
}

///|
/// [E-IntHom] 整係數同調：每個維度回傳 (自由秩, 撓不變量列表 > 1)。
pub fn cx_homology_int(cx : CellCx) -> Array[(Int32, Array[Int32])] {
  let out : Array[(Int32, Array[Int32])] = []
  for k = 0; k <= cx.dims; k = k + 1 {
    let rk = cx_rank_int(cx, k)
    let rk1 = cx_rank_int(cx, k + 1)
    let tors : Array[Int32] = []
    if k + 1 <= cx.dims {
      let dg = @core.smith_diagonal(cx.bnd[k])
      for d in dg {
        let a = if d < 0 { -d } else { d }
        if a > 1 {
          tors.push(a)
        }
      }
    }
    out.push((cx.counts[k] - rk - rk1, tors))
  }
  out
}

// ---------------------------------------------------------------------------
// 建構子
// ---------------------------------------------------------------------------

///|
pub fn cx_point(p : Int32) -> CellCx {
  cx_new([1], [], p)
}

///|
/// [D-Sphere] S^n：一個 0-胞腔 + 一個 n-胞腔（n ≥ 1 時邊界為 0）。
pub fn cx_sphere(n : Int32, p : Int32) -> CellCx {
  if n <= 0 {
    return cx_point(p)
  }
  let counts : Array[Int32] = Array::make(n + 1, 0)
  counts[0] = 1
  counts[n] = 1
  let bnd : Array[@core.Mat] = []
  for k = 0; k < n; k = k + 1 {
    bnd.push(@core.mat_make(counts[k], counts[k + 1], 0))
  }
  cx_new(counts, bnd, p)
}

///|
/// [D-Lens] 透鏡空間 L(k,1)（維度 2n+1）：每維一個胞腔，∂_{2i} = k、∂_{2i+1} = 0。
///   整係數同調：H_0 = Z、H_{2i−1} = Z/k、H_{2n+1} = Z，其餘 0。
pub fn cx_lens(k : Int32, n : Int32, p : Int32) -> CellCx {
  let d = 2 * n + 1
  let counts : Array[Int32] = Array::make(d + 1, 1)
  let bnd : Array[@core.Mat] = []
  for j = 0; j < d; j = j + 1 {
    let m = @core.mat_make(1, 1, 0)
    // ∂_{j+1}
    if (j + 1) % 2 == 0 {
      m.data[0] = k
    }
    bnd.push(m)
  }
  cx_new(counts, bnd, p)
}

///|
/// [D-Torus] T^n = (S^1)^n（用胞腔積疊出來）。
pub fn cx_torus(n : Int32, p : Int32) -> CellCx {
  let mut cx = cx_sphere(1, p)
  for _i = 1; _i < n; _i = _i + 1 {
    cx = cx_product(cx, cx_sphere(1, p))
  }
  cx
}

///|
/// [D-Leibniz] 胞腔積：cells (i,j) ↦ 維度 i+j，∂(a×b) = ∂a×b + (−1)^i a×∂b。
pub fn cx_product(a : CellCx, b : CellCx) -> CellCx {
  let p = a.p
  let d = a.dims + b.dims
  let counts : Array[Int32] = Array::make(d + 1, 0)
  for i = 0; i <= a.dims; i = i + 1 {
    for j = 0; j <= b.dims; j = j + 1 {
      counts[i + j] = counts[i + j] + a.counts[i] * b.counts[j]
    }
  }
  // 顯式填入索引
  let pos : Array[Array[Int32]] = Array::makei(a.dims + 1, _ => {
    Array::make(b.dims + 1, -1)
  })
  for dim = 0; dim <= d; dim = dim + 1 {
    let mut cursor = 0
    for i = 0; i <= a.dims; i = i + 1 {
      let j = dim - i
      if j >= 0 && j <= b.dims {
        pos[i][j] = cursor
        cursor = cursor + a.counts[i] * b.counts[j]
      }
    }
  }
  let bnd : Array[@core.Mat] = []
  for k = 0; k < d; k = k + 1 {
    // ∂_{k+1} : C_{k+1} → C_k
    let m = @core.mat_make(counts[k], counts[k + 1], 0)
    let mut col = 0
    for i = 0; i <= a.dims; i = i + 1 {
      let j = k + 1 - i
      if j >= 0 && j <= b.dims {
        for u = 0; u < a.counts[i]; u = u + 1 {
          for v = 0; v < b.counts[j]; v = v + 1 {
            // a 方向的邊界
            if i >= 1 {
              let ma = a.bnd[i - 1]
              for u0 = 0; u0 < a.counts[i - 1]; u0 = u0 + 1 {
                let c = ma.data[u0 * a.counts[i] + u]
                if c != 0 {
                  let sgn = if i % 2 == 0 { c } else { -c }
                  let row = pos[i - 1][j] + u0 * b.counts[j] + v
                  m.data[row * counts[k + 1] + col] = @core.fld_norm(
                    @core.mk_field(p),
                    m.data[row * counts[k + 1] + col] + sgn,
                  )
                }
              }
            }
            // b 方向的邊界
            if j >= 1 {
              let mb = b.bnd[j - 1]
              for v0 = 0; v0 < b.counts[j - 1]; v0 = v0 + 1 {
                let c = mb.data[v0 * b.counts[j] + v]
                if c != 0 {
                  let row = pos[i][j - 1] + v0 + u * b.counts[j - 1]
                  m.data[row * counts[k + 1] + col] = @core.fld_norm(
                    @core.mk_field(p),
                    m.data[row * counts[k + 1] + col] + c,
                  )
                }
              }
            }
            col = col + 1
          }
        }
      }
    }
    bnd.push(m)
  }
  cx_new(counts, bnd, p)
}

// ---------------------------------------------------------------------------
// 單純形 → 胞腔複形
// ---------------------------------------------------------------------------

///|
/// 在單純形列表中線性搜尋（回傳索引，找不到 −1）。
pub fn find_simplex(list : Array[Array[Int32]], s : Array[Int32]) -> Int32 {
  let mut out = -1
  let mut i = 0
  while i < list.length() && out < 0 {
    let t = list[i]
    let mut same = t.length() == s.length()
    if same {
      for k = 0; k < s.length(); k = k + 1 {
        if t[k] != s[k] {
          same = false
        }
      }
    }
    if same {
      out = i
    }
    i = i + 1
  }
  out
}

///|
/// 插入一個單純形（保持排序：先比長度再比字典序），回傳索引。
pub fn insert_simplex(list : Array[Array[Int32]], s : Array[Int32]) -> Int32 {
  let mut at = list.length()
  let mut i = 0
  let mut done = false
  while i < list.length() && !done {
    let t = list[i]
    let mut less = false
    if s.length() < t.length() {
      less = true
    } else if s.length() == t.length() {
      let mut k = 0
      let mut decided = false
      while k < s.length() && !decided {
        if s[k] < t[k] {
          less = true
          decided = true
        } else if s[k] > t[k] {
          decided = true
        }
        k = k + 1
      }
    }
    if less {
      at = i
      done = true
    }
    i = i + 1
  }
  let _ = done
  list.insert(at, s)
  at
}

///|
/// [E-Simplicial] 由「極大面」列表建立胞腔複形：自動補齊所有子面。
///   每個面是一個**遞增**的整數列表（頂點編號），定向取遞增序。
pub fn cx_from_faces(faces : Array[Array[Int32]], p : Int32) -> CellCx {
  let all : Array[Array[Int32]] = []
  for fc in faces {
    // 逐一加入所有子集
    let n = fc.length()
    for mask = 1; mask < @core.int_pow(2, n); mask = mask + 1 {
      let sub : Array[Int32] = []
      for i = 0; i < n; i = i + 1 {
        if mask / @core.int_pow(2, i) % 2 == 1 {
          sub.push(fc[i])
        }
      }
      if find_simplex(all, sub) < 0 {
        let _ = insert_simplex(all, sub)
      }
    }
  }
  // 按維度分組
  let maxd = if all.length() == 0 {
    0
  } else {
    let mut md = 0
    for s in all {
      if s.length() - 1 > md {
        md = s.length() - 1
      }
    }
    md
  }
  let bydim : Array[Array[Array[Int32]]] = Array::makei(maxd + 1, _ => [])
  for s in all {
    bydim[s.length() - 1].push(s)
  }
  let counts : Array[Int32] = Array::makei(maxd + 1, k => bydim[k].length())
  let bnd : Array[@core.Mat] = []
  for k = 0; k < maxd; k = k + 1 {
    let m = @core.mat_make(counts[k], counts[k + 1], 0)
    for j = 0; j < counts[k + 1]; j = j + 1 {
      let s = bydim[k + 1][j]
      for i = 0; i <= k + 1; i = i + 1 {
        let face : Array[Int32] = []
        for t = 0; t <= k + 1; t = t + 1 {
          if t != i {
            face.push(s[t])
          }
        }
        let row = find_simplex(bydim[k], face)
        if row >= 0 {
          let sgn = if i % 2 == 0 { 1 } else { -1 }
          m.data[row * counts[k + 1] + j] = @core.fld_norm(
            @core.mk_field(p),
            m.data[row * counts[k + 1] + j] + sgn,
          )
        }
      }
    }
    bnd.push(m)
  }
  cx_new(counts, bnd, p)
}

// ---------------------------------------------------------------------------
// 持續胞腔複形：過濾 + 條碼（標準矩陣化簡算法）
// ---------------------------------------------------------------------------

///|
/// [D-FiltCx] 帶過濾的胞腔複形：`vals[k][i]` 是 k 維第 i 個胞腔的過濾值（越小越早進入）。
pub struct FiltCx {
  cx : CellCx
  vals : Array[Array[Int32]]
}

///|
pub fn filt_const(cx : CellCx, v : Int32) -> FiltCx {
  FiltCx::{
    cx,
    vals: Array::makei(cx.dims + 1, k => Array::make(cx.counts[k], v)),
  }
}

///|
pub fn filt_with(cx : CellCx, f : (Int32, Int32) -> Int32) -> FiltCx {
  FiltCx::{
    cx,
    vals: Array::makei(cx.dims + 1, k => {
      Array::makei(cx.counts[k], i => f(k, i))
    }),
  }
}

///|
/// 依 (過濾值, 索引) 排序後的索引序列。
pub fn filt_order(vals : Array[Int32]) -> Array[Int32] {
  let n = vals.length()
  let ord : Array[Int32] = Array::makei(n, i => i)
  // 插入排序（n 很小）
  for i = 1; i < n; i = i + 1 {
    let key = ord[i]
    let mut j = i - 1
    let mut go = true
    while j >= 0 && go {
      let cur = ord[j]
      if vals[cur] > vals[key] || (vals[cur] == vals[key] && cur > key) {
        ord[j + 1] = cur
        j = j - 1
      } else {
        go = false
      }
    }
    ord[j + 1] = key
  }
  ord
}

///|
/// [E-Persist] 持續同調條碼：(維度, 出生, 死亡)，死亡 = −1 表示本質類（永不死）。
///   算法（標準矩陣化簡）：對每一維度依過濾序化簡邊界矩陣 ∂_k。
///   胞腔分兩型：
///     * **負型**：本身是主元行（其邊界有主元）⟹ 出生即死；
///     * **正型**：本身化簡為零 ⟹ 誕生一個 k 類；若之後在 ∂_{k+1} 的化簡中成為主元列，
///       就在那個 (k+1)-胞腔的過濾值處死亡；否則為本質類。
///   配對（主元列 r ← 主元行 j）即區間 (val r, val j)。
pub fn cx_barcode(f : FiltCx) -> Array[(Int32, Int32, Int32)] {
  let cx = f.cx
  let p = cx.p
  let fld = @core.mk_field(p)
  let out : Array[(Int32, Int32, Int32)] = []
  let nd = cx.dims + 1
  // 負型胞腔（本身是主元行）
  let negative : Array[Array[Bool]] = Array::makei(nd, k => {
    Array::make(cx.counts[k], false)
  })
  // 已作為主元列被更高維配對
  let paired_row : Array[Array[Bool]] = Array::makei(nd, k => {
    Array::make(cx.counts[k], false)
  })
  for k = 1; k <= cx.dims; k = k + 1 {
    let nc = cx.counts[k]
    let nr = cx.counts[k - 1]
    let ordc = filt_order(f.vals[k])
    let ordr = filt_order(f.vals[k - 1])
    let posr : Array[Int32] = Array::make(nr, 0)
    for i = 0; i < nr; i = i + 1 {
      posr[ordr[i]] = i
    }
    let reduced : Array[Array[Int32]] = Array::makei(nc, _ => [])
    let low : Array[Int32] = Array::make(nr, -1)
    let m = cx.bnd[k - 1]
    for jj = 0; jj < nc; jj = jj + 1 {
      let j = ordc[jj]
      let sorted : Array[Int32] = Array::make(nr, 0)
      for r = 0; r < nr; r = r + 1 {
        sorted[posr[r]] = @core.fld_norm(fld, m.data[r * nc + j])
      }
      let mut go = true
      while go {
        let mut piv = -1
        let mut idx = nr - 1
        while idx >= 0 && piv < 0 {
          if sorted[idx] != 0 {
            piv = idx
          }
          idx = idx - 1
        }
        if piv < 0 {
          go = false
        } else if low[piv] < 0 {
          low[piv] = jj
          reduced[jj] = sorted
          negative[k][j] = true
          let r0 = ordr[piv]
          paired_row[k - 1][r0] = true
          out.push((k - 1, f.vals[k - 1][r0], f.vals[k][j]))
          go = false
        } else {
          let j0 = low[piv]
          let factor = @core.fld_div(fld, sorted[piv], reduced[j0][piv])
          for r = 0; r < nr; r = r + 1 {
            sorted[r] = @core.fld_sub(
              fld,
              sorted[r],
              @core.fld_mul(fld, factor, reduced[j0][r]),
            )
          }
        }
      }
    }
  }
  // 本質類：正型且未被高維配對
  for k = 0; k < nd; k = k + 1 {
    for i = 0; i < cx.counts[k]; i = i + 1 {
      if !negative[k][i] && !paired_row[k][i] {
        out.push((k, f.vals[k][i], -1))
      }
    }
  }
  out
}

///|
/// [T-Persist-Betti] 持續 Betti 數：β_k(t) = #{區間 [b,d) : b ≤ t < d 或 d = −1}。
pub fn cx_persistent_betti(f : FiltCx, t : Int32) -> Array[Int32] {
  let bars = cx_barcode(f)
  let out : Array[Int32] = Array::make(f.cx.dims + 1, 0)
  for (d, b, dd) in bars {
    if b <= t && (dd < 0 || t < dd) {
      out[d] = out[d] + 1
    }
  }
  out
}

///|
/// 條碼摘要：(維度, #有限區間, #本質區間)。
pub fn cx_barcode_summary(f : FiltCx) -> Array[(Int32, Int32, Int32)] {
  let bars = cx_barcode(f)
  let out : Array[(Int32, Int32, Int32)] = []
  for d = 0; d <= f.cx.dims; d = d + 1 {
    let mut fin = 0
    let mut ess = 0
    for (d2, _b, dd) in bars {
      if d2 == d {
        if dd < 0 {
          ess = ess + 1
        } else {
          fin = fin + 1
        }
      }
    }
    out.push((d, fin, ess))
  }
  out
}
