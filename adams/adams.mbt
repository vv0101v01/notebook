// ============================================================================
// @tensorlab/adams —— 模 2 Steenrod 代數與 Adams 譜序列
// ----------------------------------------------------------------------------
// Adams 譜序列（球譜，mod 2）：
//     E_2^{s,t} = Ext_A^{s,t}(F_2, F_2)  ⟹  (π^s_{t−s})^⊗ F_2
// 其中 A 是模 2 Steenrod 代數。本檔從 Adem 關係**算出** A 的乘法表，
// 再用最小自由分解算出 Ext，最後把 E_2 放進 `@ss` 的引擎裡跑微分。
//
//   [E-Adem]     Sq^i Sq^j 的 Adem 展開（i < 2j）：Σ_k C(j−k−1, i−2k) Sq^{i+j−k} Sq^k
//   [T-Adem]     已知恆等式：Sq¹Sq¹ = 0、Sq¹Sq² = Sq³、Sq²Sq² = Sq³Sq¹、Sq²Sq³ = Sq⁵+Sq⁴Sq¹
//   [D-AdmBasis] 可容許單項式（admissible monomials）作為 A_{≤D} 的基底
//   [T-Trunc]    A_{≤D}（度數截斷）是有限維分次代數；t ≤ D 時 Ext 與完整 A 相同
//   [E-MinRes]   最小自由分解：K_s = ker(F_s → K_{s−1})，V_{s+1} = K_s / A^+K_s
//   [T-Ext-1]    Ext^{1,t} ≅ (不可分解元 Q(A)_t)^*（本檔用分解結果驗證）
//   [T-Ext-Van]  t < s 時 Ext^{s,t} = 0（對角線以下消失）
//   [E-AdamsPage] 把 Ext 表放進譜序列：p = s、q = t，微分 d_r: (s,t) → (s+r, t+r−1)
// ============================================================================

///|
/// 二項係數 mod 2（Lucas 定理）。
pub fn binom_mod2(n : Int32, k : Int32) -> Int32 {
  if k < 0 || k > n {
    return 0
  }
  let mut nn = n
  let mut kk = k
  let mut r = 1
  while nn > 0 || kk > 0 {
    let a = nn % 2
    let b = kk % 2
    if b > a {
      r = 0
    }
    nn = nn / 2
    kk = kk / 2
  }
  r
}

///|
/// 去掉 Sq^0（= 1）因子。
pub fn mono_norm(m : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in m {
    if x > 0 {
      out.push(x)
    }
  }
  out
}

///|
/// 可容許：i_k ≥ 2·i_{k+1}。
pub fn is_admissible(m : Array[Int32]) -> Bool {
  let mut ok = true
  for i = 0; i + 1 < m.length(); i = i + 1 {
    if m[i] < 2 * m[i + 1] {
      ok = false
    }
  }
  ok
}

///|
/// [E-Adem] Sq^i Sq^j 的展開（回傳各項，係數皆 1/0；模 2 相加）。
pub fn adem(i : Int32, j : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  if i >= 2 * j {
    out.push([i, j])
    return out
  }
  for k = 0; k <= i / 2; k = k + 1 {
    if binom_mod2(j - k - 1, i - 2 * k) == 1 {
      out.push(mono_norm([i + j - k, k]))
    }
  }
  out
}

///|
/// 模 2 的項集化簡：重複項相消（XOR），並正規化。
pub fn xor_terms(xs : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let drop : Array[Bool] = Array::make(xs.length(), false)
  for i = 0; i < xs.length(); i = i + 1 {
    if !drop[i] {
      let a = mono_norm(xs[i])
      for j = i + 1; j < xs.length(); j = j + 1 {
        if !drop[j] {
          let b = mono_norm(xs[j])
          let mut same = a.length() == b.length()
          if same {
            for k = 0; k < a.length(); k = k + 1 {
              if a[k] != b[k] {
                same = false
              }
            }
          }
          if same {
            drop[i] = true
            drop[j] = true
          }
        }
      }
    }
  }
  for i = 0; i < xs.length(); i = i + 1 {
    if !drop[i] {
      out.push(mono_norm(xs[i]))
    }
  }
  out
}

///|
/// 兩個單項式的乘積（回傳模 2 的項和）。
pub fn mono_mul(a : Array[Int32], b : Array[Int32]) -> Array[Array[Int32]] {
  let x = mono_norm(a)
  let y = mono_norm(b)
  if x.length() == 0 {
    return [y]
  }
  if y.length() == 0 {
    return [x]
  }
  let i = x[x.length() - 1]
  let j = y[0]
  if i >= 2 * j {
    let out : Array[Int32] = []
    for t in x {
      out.push(t)
    }
    for t in y {
      out.push(t)
    }
    return [out]
  }
  // Adem：Sq^i Sq^j = Σ_k Sq^{i+j−k} Sq^k
  let lhs : Array[Int32] = []
  for t = 0; t < x.length() - 1; t = t + 1 {
    lhs.push(x[t])
  }
  let rhs : Array[Int32] = []
  for t = 1; t < y.length(); t = t + 1 {
    rhs.push(y[t])
  }
  let acc : Array[Array[Int32]] = []
  for term in adem(i, j) {
    // k = 0 時 term = [i+j]（長度 1），Sq^0 = 1 故第二因子取 0
    let t1 = if term.length() > 1 { term[1] } else { 0 }
    let left = mono_mul(lhs, [term[0]])
    let right = mono_mul([t1], rhs)
    for p in left {
      for q in right {
        for r in mono_mul(p, q) {
          acc.push(r)
        }
      }
    }
  }
  xor_terms(acc)
}

///|
/// 生成所有度數 ≤ d 的可容許單項式（不含空單項式）。
pub fn gen_admissible(d : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  out.push([])
  let mut frontier : Array[Array[Int32]] = [[]]
  let mut deg = 0
  while deg < d {
    let next : Array[Array[Int32]] = []
    for m in frontier {
      let sum = {
        let mut s = 0
        for x in m {
          s = s + x
        }
        s
      }
      let cap = if m.length() == 0 { d } else { m[m.length() - 1] / 2 }
      for i = 1; i <= cap; i = i + 1 {
        if sum + i <= d {
          let nm : Array[Int32] = []
          for x in m {
            nm.push(x)
          }
          nm.push(i)
          out.push(nm)
          next.push(nm)
        }
      }
    }
    frontier = next
    deg = deg + 1
  }
  out
}

///|
/// 單項式的度數（Sq^i 的度數 = i）。
pub fn mono_deg(m : Array[Int32]) -> Int32 {
  let mut s = 0
  for x in m {
    s = s + x
  }
  s
}

///|
/// 把單項式陣列排序（先度數，再逐項比較）。
pub fn sort_monos(ms : Array[Array[Int32]]) -> Unit {
  for i = 1; i < ms.length(); i = i + 1 {
    let key = ms[i]
    let mut j = i - 1
    let mut go = true
    while j >= 0 && go {
      let cur = ms[j]
      let mut greater = false
      if mono_deg(cur) > mono_deg(key) {
        greater = true
      } else if mono_deg(cur) == mono_deg(key) {
        let mut k = 0
        let mut decided = false
        while k < cur.length() && k < key.length() && !decided {
          if cur[k] > key[k] {
            greater = true
            decided = true
          } else if cur[k] < key[k] {
            decided = true
          }
          k = k + 1
        }
        if !decided && cur.length() > key.length() {
          greater = true
        }
      }
      if greater {
        ms[j + 1] = cur
        j = j - 1
      } else {
        go = false
      }
    }
    ms[j + 1] = key
  }
}

///|
/// [D-StrAlg] 度數截斷的模 2 Steenrod 代數 A_{≤D}：基底 + 乘法表。
pub struct StrAlg {
  maxdeg : Int32
  basis : Array[Array[Int32]]
  deg : Array[Int32]
  tab : Array[Array[Array[Int32]]]
}

///|
/// 找單項式在基底中的索引（找不到 −1）。
pub fn mono_index(basis : Array[Array[Int32]], m : Array[Int32]) -> Int32 {
  let mm = mono_norm(m)
  let mut out = -1
  let mut i = 0
  while i < basis.length() && out < 0 {
    let b = basis[i]
    let mut same = b.length() == mm.length()
    if same {
      for k = 0; k < b.length(); k = k + 1 {
        if b[k] != mm[k] {
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
/// [T-Trunc] 建構 A_{≤D} 並算出完整乘法表（用 Adem 關係化簡）。
pub fn stralg_truncated(d : Int32) -> StrAlg {
  let basis = gen_admissible(d)
  sort_monos(basis)
  let n = basis.length()
  let deg = Array::makei(n, i => mono_deg(basis[i]))
  let tab : Array[Array[Array[Int32]]] = Array::makei(n, _ => {
    Array::makei(n, _ => Array::make(0, 0))
  })
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      if deg[i] + deg[j] <= d {
        let prod = mono_mul(basis[i], basis[j])
        let idxs : Array[Int32] = []
        for m in prod {
          let ix = mono_index(basis, m)
          if ix >= 0 {
            idxs.push(ix)
          }
        }
        tab[i][j] = xor_ids(idxs)
      }
    }
  }
  StrAlg::{ maxdeg: d, basis, deg, tab, }
}

///|
/// 索引陣列的模 2 化簡（重複者相消）。
pub fn xor_ids(xs : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  let drop : Array[Bool] = Array::make(xs.length(), false)
  for i = 0; i < xs.length(); i = i + 1 {
    if !drop[i] {
      for j = i + 1; j < xs.length(); j = j + 1 {
        if !drop[j] && xs[i] == xs[j] {
          drop[i] = true
          drop[j] = true
        }
      }
    }
  }
  for i = 0; i < xs.length(); i = i + 1 {
    if !drop[i] {
      out.push(xs[i])
    }
  }
  out
}

///|
/// 代數的維數。
pub fn stralg_dim(a : StrAlg) -> Int32 {
  a.basis.length()
}

///|
/// 不可分解元（正度數、且不能寫成兩個正度數元素之積）的度數列表。
pub fn indecomposable_degs(a : StrAlg) -> Array[Int32] {
  let n = a.basis.length()
  let out : Array[Int32] = []
  for i = 1; i < n; i = i + 1 {
    // 檢查 basis[i] 是否為某個乘積
    let mut dec = false
    for p = 1; p < n && !dec; p = p + 1 {
      for q = 1; q < n && !dec; q = q + 1 {
        if a.deg[p] + a.deg[q] == a.deg[i] {
          let prod = a.tab[p][q]
          for r in prod {
            if r == i {
              dec = true
            }
          }
        }
      }
    }
    if !dec {
      out.push(a.deg[i])
    }
  }
  out
}

// ---------------------------------------------------------------------------
// 最小自由分解 → Ext_A^{s,t}(F_2, F_2)
// ---------------------------------------------------------------------------

///|
/// F_2 上的列化簡：回傳 (秩, 化簡基底, 每個輸入是否化簡為 0)。
pub fn f2_reduce_all(
  rows : Array[Array[Int32]],
  dim : Int32,
) -> (Int32, Array[Array[Int32]]) {
  let basis : Array[Array[Int32]] = []
  let pivots : Array[Int32] = []
  for r in rows {
    let v = r.copy()
    // 用既有基底消去
    let mut changed = true
    while changed {
      changed = false
      let mut lead = -1
      let mut i = 0
      while i < dim && lead < 0 {
        if v[i] != 0 {
          lead = i
        }
        i = i + 1
      }
      if lead >= 0 {
        let mut k = 0
        while k < pivots.length() && !changed {
          if pivots[k] == lead {
            for t = 0; t < dim; t = t + 1 {
              v[t] = (v[t] + basis[k][t]) % 2
            }
            changed = true
          }
          k = k + 1
        }
      }
    }
    let mut lead = -1
    let mut i = 0
    while i < dim && lead < 0 {
      if v[i] != 0 {
        lead = i
      }
      i = i + 1
    }
    if lead >= 0 {
      basis.push(v)
      pivots.push(lead)
    }
  }
  (basis.length(), basis)
}

///|
/// 用行階梯基底 (basis, pivots) 化簡向量 v（就地回傳新向量）。
pub fn f2_reduce_vec(
  v : Array[Int32],
  basis : Array[Array[Int32]],
  pivots : Array[Int32],
  dim : Int32,
) -> Array[Int32] {
  let out = v.copy()
  let mut changed = true
  while changed {
    changed = false
    let mut lead = -1
    let mut i = 0
    while i < dim && lead < 0 {
      if out[i] != 0 {
        lead = i
      }
      i = i + 1
    }
    if lead >= 0 {
      let mut k = 0
      while k < pivots.length() && !changed {
        if pivots[k] == lead {
          for t = 0; t < dim; t = t + 1 {
            out[t] = (out[t] + basis[k][t]) % 2
          }
          changed = true
        }
        k = k + 1
      }
    }
  }
  out
}

///|
/// 矩陣（列集合）的行階梯基底與主元位置。
pub fn f2_echelon(
  rows : Array[Array[Int32]],
  dim : Int32,
) -> (Array[Array[Int32]], Array[Int32]) {
  let basis : Array[Array[Int32]] = []
  let pivots : Array[Int32] = []
  for r in rows {
    let v = f2_reduce_vec(r, basis, pivots, dim)
    let mut lead = -1
    let mut i = 0
    while i < dim && lead < 0 {
      if v[i] != 0 {
        lead = i
      }
      i = i + 1
    }
    if lead >= 0 {
      basis.push(v)
      pivots.push(lead)
    }
  }
  (basis, pivots)
}

///|
/// [E-MinRes] 計算 Ext_A^{s,t}(F_2, F_2)，s ≤ S、t ≤ T。
///   每一層：F_s = A ⊗ V_s；K_s = ker(F_s → K_{s−1})；V_{s+1} = K_s / (A^+ K_s)；
///   Ext^{s,t} = dim (K_s / A^+K_s)_t。
pub fn ext_table(
  al : StrAlg,
  s_max : Int32,
  t_max : Int32,
) -> Array[Array[Int32]] {
  let nb = al.basis.length()
  let fld = @core.mk_field(2)
  let ext : Array[Array[Int32]] = Array::makei(s_max + 1, _ => {
    Array::make(t_max + 1, 0)
  })
  ext[0][0] = 1
  // V_1：單一生成元，度數 0
  let mut vgen : Array[Int32] = [0] // 生成元的度數
  let mut vrep : Array[Array[Int32]] = [[1]] // 在 F_0 = F_2 的座標
  let mut prev_dim = 1
  let mut prev_xa : Array[Int32] = [0]
  let mut prev_xv : Array[Int32] = [0]
  let mut prev_idx : Array[Array[Int32]] = Array::makei(nb, _ => {
    Array::make(1, 0)
  })
  for s = 1; s <= s_max; s = s + 1 {
    let ng = vgen.length()
    // F_s 基底：(a, v)，度數 = deg(a) + vgen[v]
    let fs_deg : Array[Int32] = []
    let fs_a : Array[Int32] = []
    let fs_v : Array[Int32] = []
    for v = 0; v < ng; v = v + 1 {
      for i = 0; i < nb; i = i + 1 {
        if al.deg[i] + vgen[v] <= t_max {
          fs_deg.push(al.deg[i] + vgen[v])
          fs_a.push(i)
          fs_v.push(v)
        }
      }
    }
    let dimfs = fs_deg.length()
    // 由 (a, v) 查索引
    let idx : Array[Array[Int32]] = Array::makei(nb, _ => Array::make(ng, -1))
    for k = 0; k < dimfs; k = k + 1 {
      idx[fs_a[k]][fs_v[k]] = k
    }
    // φ_s：F_s → F_{s−1}
    let phi = @core.mat_make(prev_dim, dimfs, 0)
    for k = 0; k < dimfs; k = k + 1 {
      let ai = fs_a[k]
      let v = fs_v[k]
      if s == 1 {
        // F_0 = F_2 平凡模：只有 a = 1（索引 0）作用非零
        if ai == 0 {
          phi.data[0 * dimfs + k] = 1
        }
      } else {
        let rep = vrep[v]
        for x = 0; x < rep.length(); x = x + 1 {
          if rep[x] % 2 == 1 {
            // a_i · e_x，其中 e_x 是 F_{s−1} 的基向量
            for k2 in al.tab[ai][prev_xa[x]] {
              let tgt = prev_idx[k2][prev_xv[x]]
              if tgt >= 0 {
                phi.data[tgt * dimfs + k] = (phi.data[tgt * dimfs + k] + 1) % 2
              }
            }
          }
        }
      }
    }
    // K_s 依度數求核
    let kdeg : Array[Array[Array[Int32]]] = Array::makei(t_max + 1, _ => [])
    for t = 0; t <= t_max; t = t + 1 {
      // 收集度數 t 的行
      let cols : Array[Int32] = []
      for k = 0; k < dimfs; k = k + 1 {
        if fs_deg[k] == t {
          cols.push(k)
        }
      }
      if cols.length() > 0 {
        let sub = @core.mat_make(prev_dim, cols.length(), 0)
        for c = 0; c < cols.length(); c = c + 1 {
          for r = 0; r < prev_dim; r = r + 1 {
            sub.data[r * cols.length() + c] = phi.data[r * dimfs + cols[c]]
          }
        }
        let ker = @core.nullspace_basis(sub, fld)
        for kv in ker {
          // 展開回 F_s 座標
          let vec : Array[Int32] = Array::make(dimfs, 0)
          for c = 0; c < cols.length(); c = c + 1 {
            vec[cols[c]] = kv[c] % 2
          }
          kdeg[t].push(vec)
        }
      }
    }
    // W = A^+ · K_s（按目標度數收集：來源度數 = t − deg(a)）
    let wbasis_by_deg : Array[Array[Array[Int32]]] = Array::makei(t_max + 1, _ => {
      []
    })
    for t = 0; t <= t_max; t = t + 1 {
      let rows : Array[Array[Int32]] = []
      for ai = 1; ai < nb; ai = ai + 1 {
        let src = t - al.deg[ai]
        if src >= 0 {
          for kv in kdeg[src] {
            let outv : Array[Int32] = Array::make(dimfs, 0)
            for x = 0; x < dimfs; x = x + 1 {
              if kv[x] % 2 == 1 {
                for k2 in al.tab[ai][fs_a[x]] {
                  let at = idx[k2][fs_v[x]]
                  if at >= 0 {
                    outv[at] = (outv[at] + 1) % 2
                  }
                }
              }
            }
            rows.push(outv)
          }
        }
      }
      let (rk, b) = f2_reduce_all(rows, dimfs)
      wbasis_by_deg[t] = b
      ext[s][t] = kdeg[t].length() - rk
    }
    // V_{s+1}：K_s / W_s 的代表元（同一度數內做商；用行階梯消去，避免漏掉生成元）
    let nextdeg : Array[Int32] = []
    let nextrep : Array[Array[Int32]] = []
    for t = 0; t <= t_max; t = t + 1 {
      let kers = kdeg[t]
      if kers.length() > 0 {
        let (wb, wp) = f2_echelon(wbasis_by_deg[t], dimfs)
        let cb : Array[Array[Int32]] = []
        let cp : Array[Int32] = []
        for kv in kers {
          let v0 = f2_reduce_vec(kv, wb, wp, dimfs)
          let v = f2_reduce_vec(v0, cb, cp, dimfs)
          let mut lead = -1
          let mut i = 0
          while i < dimfs && lead < 0 {
            if v[i] != 0 {
              lead = i
            }
            i = i + 1
          }
          if lead >= 0 {
            cb.push(v)
            cp.push(lead)
            nextrep.push(v)
            nextdeg.push(t)
          }
        }
      }
    }
    vgen = nextdeg
    vrep = nextrep
    prev_dim = dimfs
    prev_xa = fs_a
    prev_xv = fs_v
    prev_idx = idx
    if vgen.length() == 0 {
      // 之後都是零
      return ext
    }
  }
  ext
}

///|
/// 在 (a,v) 表中查索引。
pub fn idx_at(
  as_ : Array[Int32],
  vs : Array[Int32],
  a : Int32,
  v : Int32,
) -> Int32 {
  let mut out = -1
  for k = 0; k < as_.length(); k = k + 1 {
    if as_[k] == a && vs[k] == v {
      out = k
    }
  }
  out
}

// ---------------------------------------------------------------------------
// Adams 頁：把 Ext 表放進譜序列引擎
// ---------------------------------------------------------------------------

///|
/// [E-AdamsPage] 由 Ext 表建 Adams E_2 頁：p = s（同調度）、q = t（總度數），
///   微分滿足 d_r: (s,t) → (s+r, t+r−1)，故引擎需開啟 q 方向翻轉（qflip）。
pub fn adams_page(ext : Array[Array[Int32]], p : Int32) -> @ss.Page {
  let s_max = ext.length() - 1
  let t_max = if s_max >= 0 { ext[0].length() - 1 } else { 0 }
  let page = @ss.page_new_q(2, 0, 0, s_max + 1, t_max + 1, p, true)
  for s = 0; s <= s_max; s = s + 1 {
    for t = 0; t <= t_max; t = t + 1 {
      page.dims[s][t] = ext[s][t]
    }
  }
  page
}

///|
/// Adams 譜序列中「莖」的維數：stem = t − s，故 E_2 在莖 n 上的維數 = Σ_{t−s=n} Ext^{s,t}。
pub fn adams_stem_dims(
  page : @ss.Page,
  s_max : Int32,
  t_max : Int32,
) -> Array[Int32] {
  let out : Array[Int32] = Array::make(t_max + 1, 0)
  for s = 0; s <= s_max; s = s + 1 {
    for t = 0; t <= t_max; t = t + 1 {
      let stem = t - s
      if stem >= 0 && stem <= t_max {
        out[stem] = out[stem] + @ss.page_dim(page, s, t)
      }
    }
  }
  out
}
