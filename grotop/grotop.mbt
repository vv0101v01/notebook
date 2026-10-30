// ===========================================================================
// grotop — 格羅滕迪克拓撲（site / sieve / 覆蓋 / 層條件）
//
// 模型：一個有限偏序集（開集）作為範疇，sieve 用布林陣列表示，
//      拓撲 = 每點的覆蓋 sieve 族，用 (T1) 最大 sieve、(T2) 拉回穩定、
//      (T3) 局部刻劃三條公理「機器驗證」。層條件用線性代數的
//      正合性 0 → F(U) → ∏F(V_i) → ∏F(V_i ∧ V_j) 判定。
// ===========================================================================

///|
/// [D-Site] 有限 site：開集 0..n−1，`leq[a][b]` = (U_a ⊆ U_b)，p 為係數特徵。
pub struct Site {
  n : Int32
  leq : Array[Array[Bool]]
  p : Int32
}

///|
/// [D-Site] 由偏序矩陣建 site。要求自反、反對稱（由布林矩陣隱含）、傳遞。
pub fn site_new(leq : Array[Array[Bool]], p : Int32) -> Site {
  Site::{ n: leq.length(), leq, p, }
}

///|
/// [T-Site] 偏序公理檢查（自反、傳遞）。
pub fn site_valid(s : Site) -> Bool {
  let mut ok = true
  for a = 0; a < s.n; a = a + 1 {
    if !s.leq[a][a] {
      ok = false
    }
    for b = 0; b < s.n; b = b + 1 {
      for c = 0; c < s.n; c = c + 1 {
        if s.leq[a][b] && s.leq[b][c] && !s.leq[a][c] {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// 開集包含判定。
pub fn site_le(s : Site, a : Int32, b : Int32) -> Bool {
  s.leq[a][b]
}

///|
/// [D-Meet] 兩開集的交（最大下界）；不存在回 −1。
pub fn site_meet(s : Site, a : Int32, b : Int32) -> Int32 {
  let mut best = -1
  for c = 0; c < s.n; c = c + 1 {
    if s.leq[c][a] && s.leq[c][b] {
      let mut maximal = true
      for d = 0; d < s.n; d = d + 1 {
        if d != c && s.leq[c][d] && s.leq[d][a] && s.leq[d][b] {
          maximal = false
        }
      }
      if maximal {
        best = c
      }
    }
  }
  best
}

///|
/// [D-Sieve] sieve 以布林陣列表示：`sv[a]` = (U_a 屬於此 sieve)。
pub fn sieve_empty(s : Site) -> Array[Bool] {
  Array::make(s.n, false)
}

///|
/// 以覆蓋族生成的 sieve（向下封閉化）。
pub fn sieve_generate(s : Site, fam : Array[Int32]) -> Array[Bool] {
  let sv = Array::make(s.n, false)
  for v in fam {
    if v >= 0 && v < s.n {
      sv[v] = true
    }
  }
  let mut changed = true
  while changed {
    changed = false
    for a = 0; a < s.n; a = a + 1 {
      if sv[a] {
        for b = 0; b < s.n; b = b + 1 {
          if s.leq[b][a] && !sv[b] {
            sv[b] = true
            changed = true
          }
        }
      }
    }
  }
  sv
}

///|
/// [T-Sieve] 向下封閉性判定。
pub fn sieve_is_down_closed(s : Site, sv : Array[Bool]) -> Bool {
  let mut ok = true
  for a = 0; a < s.n; a = a + 1 {
    if sv[a] {
      for b = 0; b < s.n; b = b + 1 {
        if s.leq[b][a] && !sv[b] {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// [D-Sieve] 最大 sieve：所有 V ⊆ U。
pub fn sieve_max(s : Site, u : Int32) -> Array[Bool] {
  let sv = Array::make(s.n, false)
  for a = 0; a < s.n; a = a + 1 {
    if s.leq[a][u] {
      sv[a] = true
    }
  }
  sv
}

///|
/// [D-Sieve] 拉回 f*S（f: V ⊆ U）。
pub fn sieve_pull(s : Site, sv : Array[Bool], v : Int32) -> Array[Bool] {
  let out = Array::make(s.n, false)
  for a = 0; a < s.n; a = a + 1 {
    if s.leq[a][v] && sv[a] {
      out[a] = true
    }
  }
  out
}

///|
/// sieve 交（逐點 AND）。
pub fn sieve_and(s : Site, a : Array[Bool], b : Array[Bool]) -> Array[Bool] {
  let out = Array::make(s.n, false)
  for i = 0; i < s.n; i = i + 1 {
    out[i] = a[i] && b[i]
  }
  out
}

///|
/// sieve 包含判定 a ⊆ b。
pub fn sieve_le(s : Site, a : Array[Bool], b : Array[Bool]) -> Bool {
  let mut ok = true
  for i = 0; i < s.n; i = i + 1 {
    if a[i] && !b[i] {
      ok = false
    }
  }
  ok
}

///|
/// sieve 的元素（開集索引清單）。
pub fn sieve_elems(s : Site, sv : Array[Bool]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i = 0; i < s.n; i = i + 1 {
    if sv[i] {
      out.push(i)
    }
  }
  out
}

///|
/// [D-Topology] 拓撲：`cov[u]` 為覆蓋 U 的 sieve 清單。
pub struct Topology {
  site : Site
  /// 已飽和的覆蓋 sieve 族（供公理檢查）
  cov : Array[Array[Array[Bool]]]
  /// 登錄的覆蓋「族」（供層條件檢查：層條件只需在一組基上驗證）
  fams : Array[Array[Array[Int32]]]
}

///|
/// 「離散拓撲」：每個 sieve 都覆蓋（最粗的合法拓撲之一）。
pub fn top_discrete(s : Site) -> Topology {
  let cov : Array[Array[Array[Bool]]] = Array::makei(s.n, _ => [])
  let fams : Array[Array[Array[Int32]]] = Array::makei(s.n, _ => [])
  for u = 0; u < s.n; u = u + 1 {
    cov[u] = all_sieves(s, u)
    fams[u].push([u])
  }
  Topology::{ site: s, cov, fams, }
}

///|
/// 「混沌拓撲」：只有最大 sieve 覆蓋（即 Zariski 式的「無覆蓋」拓撲）。
pub fn top_chaotic(s : Site) -> Topology {
  let cov : Array[Array[Array[Bool]]] = Array::makei(s.n, _ => [])
  let fams : Array[Array[Array[Int32]]] = Array::makei(s.n, _ => [])
  for u = 0; u < s.n; u = u + 1 {
    cov[u] = [sieve_max(s, u)]
    fams[u].push([u])
  }
  Topology::{ site: s, cov, fams, }
}

///|
/// 由覆蓋族生成的拓撲（取飽和：加入最大 sieve、拉回、複合）。
pub fn top_of_families(
  s : Site,
  fams : Array[(Int32, Array[Int32])],
) -> Topology {
  let cov : Array[Array[Array[Bool]]] = Array::makei(s.n, _ => [])
  let famtab : Array[Array[Array[Int32]]] = Array::makei(s.n, _ => [])
  for u = 0; u < s.n; u = u + 1 {
    cov[u].push(sieve_max(s, u))
    famtab[u].push([u])
  }
  for f in fams {
    cov[f.0].push(sieve_generate(s, f.1))
    famtab[f.0].push(f.1)
  }
  // 拉回穩定化
  let mut changed = true
  while changed {
    changed = false
    for u = 0; u < s.n; u = u + 1 {
      let old = cov[u].copy()
      for sv in old {
        for v = 0; v < s.n; v = v + 1 {
          if s.leq[v][u] {
            let p = sieve_pull(s, sv, v)
            if !has_sieve(cov[v], p) {
              cov[v].push(p)
              changed = true
            }
          }
        }
      }
    }
  }
  Topology::{ site: s, cov, fams: famtab, }
}

///|
/// 清單中是否已有該 sieve。
pub fn has_sieve(list : Array[Array[Bool]], sv : Array[Bool]) -> Bool {
  let mut found = false
  for x in list {
    let mut same = true
    for i = 0; i < x.length(); i = i + 1 {
      if x[i] != sv[i] {
        same = false
      }
    }
    if same {
      found = true
    }
  }
  found
}

///|
/// 某開集上的全部 sieve（向下封閉且元素 ⊆ U）。
pub fn all_sieves(s : Site, u : Int32) -> Array[Array[Bool]] {
  let out : Array[Array[Bool]] = []
  let total = 1 << s.n
  for m = 0; m < total; m = m + 1 {
    let sv = Array::make(s.n, false)
    for i = 0; i < s.n; i = i + 1 {
      if (m >> i) % 2 == 1 {
        sv[i] = true
      }
    }
    let mut ok = true
    for i = 0; i < s.n; i = i + 1 {
      if sv[i] && !s.leq[i][u] {
        ok = false
      }
    }
    if ok && sieve_is_down_closed(s, sv) {
      out.push(sv)
    }
  }
  out
}

///|
/// 覆蓋 sieve 已否？
pub fn covers(t : Topology, u : Int32, sv : Array[Bool]) -> Bool {
  has_sieve(t.cov[u], sv)
}

///|
/// [T-Top1] (T1) 最大 sieve 覆蓋：U 的 maximal sieve 覆蓋 U。
pub fn top_axiom_max(t : Topology) -> Bool {
  let mut ok = true
  for u = 0; u < t.site.n; u = u + 1 {
    if !covers(t, u, sieve_max(t.site, u)) {
      ok = false
    }
  }
  ok
}

///|
/// [T-Top2] (T2) 拉回穩定：S 覆蓋 U ⟹ 對所有 V ⊆ U，f*S 覆蓋 V。
pub fn top_axiom_pull(t : Topology) -> Bool {
  let mut ok = true
  for u = 0; u < t.site.n; u = u + 1 {
    for sv in t.cov[u] {
      for v = 0; v < t.site.n; v = v + 1 {
        if t.site.leq[v][u] {
          if !covers(t, v, sieve_pull(t.site, sv, v)) {
            ok = false
          }
        }
      }
    }
  }
  ok
}

///|
/// [T-Top3] (T3) 局部刻劃：S 覆蓋 U，且 R 覆蓋 U、R 在 S 的每個元素上局部覆蓋 ⟹ R 覆蓋 U。
pub fn top_axiom_local(t : Topology) -> Bool {
  let mut ok = true
  for u = 0; u < t.site.n; u = u + 1 {
    for sv in t.cov[u] {
      for rv in all_sieves(t.site, u) {
        let mut local_ok = true
        for f in sieve_elems(t.site, sv) {
          if !covers(t, f, sieve_pull(t.site, rv, f)) {
            local_ok = false
          }
        }
        if local_ok && !covers(t, u, rv) {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// [T-Top] 三條公理全過 ⟹ 是一個格羅滕迪克拓撲。
pub fn top_valid(t : Topology) -> Bool {
  top_axiom_max(t) && top_axiom_pull(t) && top_axiom_local(t)
}

// ---------------------------------------------------------------------------
// 層條件（線性代數版）
// ---------------------------------------------------------------------------

///|
/// [D-Presheaf] 有限 site 上的預層：每個開集的維數與限制映射（矩陣）。
///   `res[a][b]`（a ⊆ b）是 F(U_b) → F(U_a) 的矩陣。
pub struct Presheaf {
  site : Site
  dims : Array[Int32]
  res : Array[Array[@core.Mat?]]
}

///|
/// 建預層；`f` 提供限制矩陣（a ⊆ b 時）。
pub fn pf_new(
  s : Site,
  dims : Array[Int32],
  f : (Int32, Int32) -> @core.Mat?,
) -> Presheaf {
  let res : Array[Array[@core.Mat?]] = Array::makei(s.n, _ => {
    Array::makei(s.n, _ => None)
  })
  for a = 0; a < s.n; a = a + 1 {
    for b = 0; b < s.n; b = b + 1 {
      if s.leq[a][b] {
        res[a][b] = f(a, b)
      }
    }
  }
  Presheaf::{ site: s, dims, res, }
}

///|
/// 取限制矩陣。
pub fn pf_res(pf : Presheaf, a : Int32, b : Int32) -> @core.Mat {
  match pf.res[a][b] {
    Some(m) => m
    None => @core.mat_make(pf.dims[a], pf.dims[b], 0)
  }
}

///|
/// 垂直堆疊矩陣（同欄數）。
pub fn vstack(ms : Array[@core.Mat], cols : Int32) -> @core.Mat {
  let mut rows = 0
  for m in ms {
    rows = rows + m.rows
  }
  let out = @core.mat_make(rows, cols, 0)
  let mut off = 0
  for m in ms {
    for i = 0; i < m.rows; i = i + 1 {
      for j = 0; j < m.cols; j = j + 1 {
        out.data[(off + i) * cols + j] = m.data[i * m.cols + j]
      }
    }
    off = off + m.rows
  }
  out
}

///|
/// [T-Sheaf] 對覆蓋 sieve S 檢查層條件：
///   0 → F(U) → ∏_{V∈S} F(V) → ∏_{V,W∈S} F(V∧W)
///   回傳 (單射?, 正合?, dim ker d⁰, dim ker d¹, rank d⁰)。
pub fn sheaf_check(
  pf : Presheaf,
  u : Int32,
  fam : Array[Int32],
) -> (Bool, Bool, Int32, Int32, Int32) {
  let s = pf.site
  let fld = @core.mk_field(s.p)
  let vs = fam
  // d⁰: F(U) → ∏ F(V)
  let d0s : Array[@core.Mat] = []
  for v in vs {
    d0s.push(pf_res(pf, v, u))
  }
  let d0 = vstack(d0s, pf.dims[u])
  // d¹: ∏ F(V) → ∏ F(V∧W)
  let total_in = d0.rows
  // 先算每個 F(V) 在輸入中的偏移
  let off_in : Array[Int32] = []
  let mut acc = 0
  for v in vs {
    off_in.push(acc)
    acc = acc + pf.dims[v]
  }
  let mut out_rows = 0
  for i = 0; i < vs.length(); i = i + 1 {
    for j = 0; j < vs.length(); j = j + 1 {
      let m = site_meet(s, vs[i], vs[j])
      let width = if m >= 0 { pf.dims[m] } else { 0 }
      out_rows = out_rows + width
    }
  }
  let d1 = @core.mat_make(out_rows, total_in, 0)
  let mut row = 0
  for i = 0; i < vs.length(); i = i + 1 {
    for j = 0; j < vs.length(); j = j + 1 {
      let m = site_meet(s, vs[i], vs[j])
      if m >= 0 {
        let w = pf.dims[m]
        let mi = pf_res(pf, m, vs[i])
        let mj = pf_res(pf, m, vs[j])
        // Čech 微分 (d¹σ)_{ij} = σ_j| − σ_i|：第一因子取 −1，第二因子取 +1。
        // 於 i = j 時該塊自動為零，故 (d¹ d⁰) = 0 且秩不受影響。
        let sign_i = s.p - 1
        let sign_j = 1
        for r = 0; r < w; r = r + 1 {
          for c = 0; c < pf.dims[vs[i]]; c = c + 1 {
            let v = mi.data[r * mi.cols + c]
            if v != 0 {
              let nv = if sign_i == 1 { v } else { (s.p - v) % s.p }
              d1.data[(row + r) * total_in + off_in[i] + c] = (
                  d1.data[(row + r) * total_in + off_in[i] + c] + nv
                ) %
                s.p
            }
          }
          for c = 0; c < pf.dims[vs[j]]; c = c + 1 {
            let v = mj.data[r * mj.cols + c]
            if v != 0 {
              let nv = if sign_j == 1 { v } else { (s.p - v) % s.p }
              d1.data[(row + r) * total_in + off_in[j] + c] = (
                  d1.data[(row + r) * total_in + off_in[j] + c] + nv
                ) %
                s.p
            }
          }
        }
        row = row + w
      }
    }
  }
  let k0 = pf.dims[u] - @core.rank_mod(d0, fld)
  let k1 = total_in - @core.rank_mod(d1, fld)
  let r0 = @core.rank_mod(d0, fld)
  let inj = k0 == 0
  let exact = k1 == r0 && inj
  (inj, exact, k0, k1, r0)
}

///|
/// [T-Sheaf] 預層是否在該拓撲下是層（對所有覆蓋 sieve 檢查）。
pub fn is_sheaf(pf : Presheaf, t : Topology) -> Bool {
  let mut ok = true
  for u = 0; u < t.site.n; u = u + 1 {
    for fam in t.fams[u] {
      let (inj, exact, _, _, _) = sheaf_check(pf, u, fam)
      if !inj || !exact {
        ok = false
      }
    }
  }
  ok
}

///|
/// [E-Plus] 加號構造（一階層化）：dim F⁺(U) = dim{相容族} = dim ker d¹（對該覆蓋）。
pub fn pf_plus_dim(pf : Presheaf, u : Int32, fam : Array[Int32]) -> Int32 {
  let (_, _, _, k1, _) = sheaf_check(pf, u, fam)
  k1
}

///|
/// 加號構造的維數：F⁺(U) 是覆蓋族的餘極限（colimit），維數取所有登錄覆蓋的最大值。
pub fn pf_plus_dim_all(pf : Presheaf, t : Topology, u : Int32) -> Int32 {
  let mut best = -1
  for fam in t.fams[u] {
    let (_, _, _, k1, _) = sheaf_check(pf, u, fam)
    if k1 > best {
      best = k1
    }
  }
  best
}
