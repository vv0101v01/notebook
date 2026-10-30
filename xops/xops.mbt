// ===========================================================================
// xops — 交叉運算：扭曲 K 理論 × 非交叉樹 × 格羅滕迪克拓撲 × 扭曲 AHSS
//
// 四個交互定理：
//   [T-X-Vanish]   H³(X;Z) = 0 ⟹ twist 不可見（d_3 = Sq³ = 0，dim X ≤ 5）
//   [T-X-Sum]      不相交並的扭曲 AHSS 可加：E_∞(X ⊔ Y) = E_∞(X) ⊕ E_∞(Y)
//   [T-X-Site]     非交叉森林上的「分量覆蓋」是格羅滕迪克拓撲；
//                  弦上的函數層 F(U) = F_p^{|U|} 對它是層
//   [T-X-Obstruct] 局部給定的 twist 類要能黏成整體類的障礙 = k¹ − r⁰
//                  （格羅滕迪克拓撲 × 扭曲 AHSS 的可計算交互不變量）
// ===========================================================================

///|
/// [E-X-Vanish] twist 只在 H³ 有類時可見：dim H³ = 0 ⟹ d_3 的 twist 部分為零。
pub fn xops_twist_visible(alg : @ahss.Alg) -> Bool {
  @ahss.alg_dim(alg, 3) > 0
}

///|
/// [E-X-Sum] 分次代數的不相交並：H^k(A ⊔ B) = H^k(A) ⊕ H^k(B)（跨項乘積為 0）。
pub fn alg_sum(a : @ahss.Alg, b : @ahss.Alg) -> @ahss.Alg {
  let top = if a.top > b.top { a.top } else { b.top }
  let dims : Array[Int32] = Array::makei(top + 1, k => {
    @ahss.alg_dim(a, k) + @ahss.alg_dim(b, k)
  })
  let alg = @ahss.alg_skeleton(dims, a.p)
  for i = 0; i <= top; i = i + 1 {
    for j = 0; i + j <= top; j = j + 1 {
      let m = @core.mat_make(dims[i + j], dims[i] * dims[j], 0)
      let ca = @ahss.alg_get_cup(a, i, j)
      let cb = @ahss.alg_get_cup(b, i, j)
      // 欄索引：(summand, a-index, b-index)
      for pa = 0; pa < dims[i]; pa = pa + 1 {
        for pb = 0; pb < dims[j]; pb = pb + 1 {
          // A 部分
          if pa < @ahss.alg_dim(a, i) && pb < @ahss.alg_dim(a, j) {
            for r = 0; r < @ahss.alg_dim(a, i + j); r = r + 1 {
              m.data[r * m.cols + pa * dims[j] + pb] = ca.data[r * ca.cols +
                pa * @ahss.alg_dim(a, j) +
                pb]
            }
          }
          // B 部分
          if pa < @ahss.alg_dim(b, i) && pb < @ahss.alg_dim(b, j) {
            let off_t = @ahss.alg_dim(a, i + j)
            for r = 0; r < @ahss.alg_dim(b, i + j); r = r + 1 {
              m.data[(off_t + r) * m.cols + pa * dims[j] + pb] = cb.data[r *
                cb.cols +
                pa * @ahss.alg_dim(b, j) +
                pb]
            }
          }
        }
      }
      @ahss.alg_set_cup(alg, i, j, m)
    }
  }
  alg
}

///|
/// 兩頁的維數表在重疊範圍內是否相等。
pub fn page_dims_eq(a : @ss.Page, b : @ss.Page) -> Bool {
  let mut ok = true
  for i = 0; i < a.np; i = i + 1 {
    for j = 0; j < a.nq; j = j + 1 {
      if @ss.page_dim(a, i, j) != @ss.page_dim(b, i, j) {
        ok = false
      }
    }
  }
  ok
}

// ---------------------------------------------------------------------------
// 非交叉森林 site
// ---------------------------------------------------------------------------

///|
/// [D-X-Forest] n 邊形的非交叉森林：以弦集合的位元遮罩表示。
///   `chord_list(n)` 的索引 i 對應弦 (a,b)。
pub fn chord_list(n : Int32) -> Array[(Int32, Int32)] {
  let out : Array[(Int32, Int32)] = []
  for a = 0; a < n; a = a + 1 {
    for b = a + 1; b < n; b = b + 1 {
      out.push((a, b))
    }
  }
  out
}

///|
/// 遮罩（森林）是否非交叉。
pub fn forest_noncrossing(n : Int32, mask : Int32) -> Bool {
  let cl = chord_list(n)
  let mut ok = true
  for i = 0; i < cl.length(); i = i + 1 {
    for j = i + 1; j < cl.length(); j = j + 1 {
      if (mask >> i) % 2 == 1 && (mask >> j) % 2 == 1 {
        let x = @nc.chord(cl[i].0, cl[i].1)
        let y = @nc.chord(cl[j].0, cl[j].1)
        if @nc.chords_cross(x, y) {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// 遮罩中弦的個數。
pub fn mask_popcount(mask : Int32) -> Int32 {
  let mut c = 0
  let mut m = mask
  while m > 0 {
    c = c + m % 2
    m = m / 2
  }
  c
}

///|
/// 並查集找根。
fn uf_find(p : Array[Int32], x : Int32) -> Int32 {
  let mut cur = x
  while p[cur] != cur {
    cur = p[cur]
  }
  cur
}

///|
/// 森林的連通分量（每個分量以遮罩表示）。
pub fn forest_components(n : Int32, mask : Int32) -> Array[Int32] {
  let cl = chord_list(n)
  // 並查集
  let par : Array[Int32] = Array::makei(n, i => i)
  for i = 0; i < cl.length(); i = i + 1 {
    if (mask >> i) % 2 == 1 {
      let ra = uf_find(par, cl[i].0)
      let rb = uf_find(par, cl[i].1)
      if ra != rb {
        par[ra] = rb
      }
    }
  }
  // 收集每個根對應的弦遮罩
  let roots : Array[Int32] = []
  for v = 0; v < n; v = v + 1 {
    let r = uf_find(par, v)
    let mut seen = false
    for x in roots {
      if x == r {
        seen = true
      }
    }
    if !seen {
      roots.push(r)
    }
  }
  let out : Array[Int32] = []
  for r in roots {
    let mut m = 0
    for i = 0; i < cl.length(); i = i + 1 {
      if (mask >> i) % 2 == 1 && uf_find(par, cl[i].0) == r {
        m = m + (1 << i)
      }
    }
    if m > 0 {
      out.push(m)
    }
  }
  out
}

///|
/// [E-X-Site] 非交叉森林上的 site：開集 = 非交叉森林，偏序 = 遮罩包含。
pub fn xops_nc_site(n : Int32, p : Int32) -> @grotop.Site {
  let total = @core.int_pow(2, n * (n - 1) / 2)
  let masks : Array[Int32] = []
  for m = 0; m < total; m = m + 1 {
    if forest_noncrossing(n, m) {
      masks.push(m)
    }
  }
  let k = masks.length()
  let leq : Array[Array[Bool]] = Array::makei(k, _ => Array::make(k, false))
  for i = 0; i < k; i = i + 1 {
    for j = 0; j < k; j = j + 1 {
      if (masks[i] & masks[j]) == masks[i] {
        leq[i][j] = true
      }
    }
  }
  @grotop.site_new(leq, p)
}

///|
/// site 中遮罩對應的索引。
pub fn site_index(n : Int32, mask : Int32) -> Int32 {
  let total = @core.int_pow(2, n * (n - 1) / 2)
  let mut res = -1
  let mut c = 0
  for m = 0; m < total; m = m + 1 {
    if forest_noncrossing(n, m) {
      if m == mask {
        res = c
      }
      c = c + 1
    }
  }
  res
}

///|
/// [T-X-Site] 「分量覆蓋」族：每個森林由它的連通分量覆蓋；∅ 只由自己覆蓋。
pub fn xops_nc_families(n : Int32) -> Array[(Int32, Array[Int32])] {
  let total = @core.int_pow(2, n * (n - 1) / 2)
  let out : Array[(Int32, Array[Int32])] = []
  for m = 0; m < total; m = m + 1 {
    if forest_noncrossing(n, m) {
      let u = site_index(n, m)
      if u >= 0 {
        let comps = forest_components(n, m)
        let fam : Array[Int32] = []
        if comps.length() == 0 {
          fam.push(u) // ∅ 由自己覆蓋
        } else {
          for c in comps {
            let ci = site_index(n, c)
            if ci >= 0 {
              fam.push(ci)
            }
          }
        }
        out.push((u, fam))
      }
    }
  }
  out
}

///|
/// [T-X-Site] 建立非交叉森林的格羅滕迪克拓撲。
pub fn xops_nc_topology(n : Int32, p : Int32) -> @grotop.Topology {
  let s = xops_nc_site(n, p)
  @grotop.top_of_families(s, xops_nc_families(n))
}

///|
/// [T-X-Obstruct] twist 局部系統的黏合障礙：對每個覆蓋取 k¹ − r⁰（正合性缺口）。
pub fn xops_twist_obstruction(
  pf : @grotop.Presheaf,
  t : @grotop.Topology,
) -> Int32 {
  let mut total = 0
  for u = 0; u < t.site.n; u = u + 1 {
    for fam in t.fams[u] {
      let (_, _, _, k1, r0) = @grotop.sheaf_check(pf, u, fam)
      if k1 > r0 {
        total = total + (k1 - r0)
      }
    }
  }
  total
}

///|
/// [T-X-Koszul] Koszul 對偶的一組獨立驗證（兩個不同引擎算同一個結構的兩面）：
///   V = F_2^g，A = Λ(V)（g 個度數 1 的生成元）時
///     Ext_A(F_2,F_2) 由 `@adams` 的最小自由分解算出：(i,i) 上恆為 1（= Sym(V*)）；
///   而 B = Sym(V) 時
///     Tor^B_i(F_2,F_2) 由 `@dtensor` 的兩份自由分解算出：dim = C(2g, i)（= Λ(V⊕V)）。
///   回傳 (Ext 維數, Tor 維數)。
pub fn xops_koszul_pair(g : Int32, i : Int32) -> (Int32, Int32) {
  // Λ(V)：截斷 Steenrod 代數在 D = 1 時就是 Λ(Sq¹)，此處改用 g 個生成元的代數需 D ≥ g，
  // 故以 D = g 的截斷代數之低度數部分讀出 (i,i) 的 Ext。
  let d = if g < 1 { 1 } else { g }
  let ext = @adams.ext_table(@adams.stralg_truncated(d), i, i)
  let tor = @dtensor.tor_dim(@dtensor.poly_alg(g, 2 * g + 2), i, i)
  (ext[i][i], tor)
}
