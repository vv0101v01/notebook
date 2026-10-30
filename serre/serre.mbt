// ============================================================================
// @tensorlab/serre —— 塞爾譜序列（Serre spectral sequence）
// ----------------------------------------------------------------------------
// 對纖維化 F → E → B（餘調版）：
//     E_2^{p,q} = H^p(B; H^q(F; ρ))  ⟹  H^{p+q}(E)
// 同調版：E^2_{p,q} = H_p(B; H_q(F; ρ)) ⟹ H_{p+q}(E)。
// 本檔用 `@ss` 的引擎把它算出來，並用 `@cellcx` 獨立算出的 E 的同調做交叉驗證：
//
//   [D-Serre-E2]   E^2 = H_*(B) ⊗ H_*(F)（域係數、Künneth 無 Tor；扭轉係數取 coinvariants）
//   [T-Serre-Hopf] S^1 → S^3 → S^2：d_2 是 Euler 類 e 給出的同構 ⟹ E_∞ 只在總次數 0、3
//   [T-Serre-Bundle] S^n → S^{2n+1} → S^{n+1}：d_{n+1} = e·（transgression）
//   [T-Serre-Deg]  當 E^2 只有 (0,0) 與 (0,n) 兩列時，所有微分必為零（邊緣退化）
//   [T-Serre-Twist] 扭轉係數（單值化）：H_0(F;ρ) = coinvariants，H^0(F;ρ) = invariants
//   [E-Serre-Run]  反覆取下一頁直到微分全零（或步數用盡）⟹ E_∞
// ============================================================================

///|
/// [D-Serre-E2] 由 B、F 的 Betti 數建 E^2 頁（r = 2，全部微分為零）。
pub fn serre_e2(bb : Array[Int32], bf : Array[Int32], p : Int32) -> @ss.Page {
  let page = @ss.page_new(2, 0, 0, bb.length(), bf.length(), p)
  for i = 0; i < bb.length(); i = i + 1 {
    for j = 0; j < bf.length(); j = j + 1 {
      page.dims[i][j] = bb[i] * bf[j]
    }
  }
  page
}

///|
/// [E-Serre-Run] 反覆 `page_next`，直到微分全零或走到 `steps` 頁。
pub fn serre_run(page : @ss.Page, steps : Int32) -> @ss.Page {
  let mut cur = page
  let mut k = 0
  let mut done = false
  while k < steps && !done {
    if @ss.page_zero_diffs(cur) {
      done = true
    } else {
      cur = @ss.page_next(cur)
      k = k + 1
    }
  }
  cur
}

///|
/// S^{n+1} 的 Betti 數。
pub fn sphere_betti(m : Int32) -> Array[Int32] {
  let b = Array::make(m + 1, 0)
  b[0] = 1
  b[m] = 1
  b
}

///|
/// [T-Serre-Bundle] 球叢 S^n → E → S^{n+1} 的 E^2 頁，微分 d_{n+1} = e（Euler 數）。
pub fn sphere_bundle(n : Int32, e : Int32, p : Int32) -> @ss.Page {
  let page = serre_e2(sphere_betti(n + 1), sphere_betti(n), p)
  // 把頁的 r 改成 n+1：d_{n+1}: E^{0,n} → E^{n+1,0}
  let out = @ss.page_new(n + 1, 0, 0, n + 2, n + 1, p)
  for i = 0; i <= n + 1; i = i + 1 {
    for j = 0; j <= n; j = j + 1 {
      out.dims[i][j] = page.dims[i][j]
    }
  }
  let m = @core.mat_make(1, 1, 0)
  m.data[0] = @core.fld_norm(@core.mk_field(p), e)
  @ss.page_setd_at(out, 0, n, m)
  out
}

///|
/// [T-Serre-Hopf] Hopf 纖維化 S^1 → S^3 → S^2。
pub fn hopf(e : Int32, p : Int32) -> @ss.Page {
  sphere_bundle(1, e, p)
}

///|
/// [T-Serre-Hopf] E_∞ 的總維數是否等於 S^{2n+1} 的同調（即 d_{n+1} 非零時的收斂）。
pub fn serre_sphere_converges(n : Int32, e : Int32, p : Int32) -> Bool {
  let page = sphere_bundle(n, e, p)
  let fin = serre_run(page, 4)
  let (fit, exact) = @ss.page_converges(fin, sphere_betti(2 * n + 1))
  fit && exact
}

///|
/// [T-Serre-Deg] 邊緣退化判準：若 E^2 只佔 p = 0 與 p = m 兩行且 m ≥ 2，
///   則所有 d_r 都落在窗外 ⟹ E_∞ = E^2（以維數表比較）。
pub fn serre_degenerate_two_columns(page : @ss.Page) -> Bool {
  let mut ok = true
  for i = 0; i < page.np; i = i + 1 {
    for j = 0; j < page.nq; j = j + 1 {
      if page.dims[i][j] > 0 && i != 0 {
        // 非零只允許在最後一列（p = np−1）
        if i != page.np - 1 {
          ok = false
        }
      }
    }
  }
  ok
}

// ---------------------------------------------------------------------------
// 扭轉係數（單值化）
// ---------------------------------------------------------------------------

///|
/// [T-Serre-Twist] 不變量維數 dim V^{⟨g⟩} = dim ⋂ ker(g − I)：
///   堆疊所有 (g_i − I) 成矩陣，取核。
pub fn invariants_dim(v : Int32, gens : Array[@core.Mat], p : Int32) -> Int32 {
  if gens.length() == 0 {
    return v
  }
  let fld = @core.mk_field(p)
  // 每個生成元先減去單位矩陣：(g − I) 的核 = 固定點
  let minus : Array[@core.Mat] = []
  for g in gens {
    let m = @core.mat_copy(g)
    for i = 0; i < v; i = i + 1 {
      m.data[i * v + i] = @core.fld_sub(fld, m.data[i * v + i], 1)
    }
    minus.push(m)
  }
  let mut cur = minus[0]
  let mut k = 1
  while k < minus.length() {
    let rows = cur.rows + minus[k].rows
    let m = @core.mat_make(rows, v, 0)
    for i = 0; i < cur.rows; i = i + 1 {
      for j = 0; j < v; j = j + 1 {
        m.data[i * v + j] = cur.data[i * v + j]
      }
    }
    for i = 0; i < minus[k].rows; i = i + 1 {
      for j = 0; j < v; j = j + 1 {
        m.data[(cur.rows + i) * v + j] = minus[k].data[i * v + j]
      }
    }
    cur = m
    k = k + 1
  }
  v - @core.rank_mod(cur, fld)
}

///|
/// [T-Serre-Twist] 餘不變量維數 dim V_{⟨g⟩} = v − rank(span{g_i − I})。
pub fn coinvariants_dim(v : Int32, gens : Array[@core.Mat], p : Int32) -> Int32 {
  if gens.length() == 0 {
    return v
  }
  let fld = @core.mk_field(p)
  let rows = v * gens.length()
  let m = @core.mat_make(rows, v, 0)
  for g = 0; g < gens.length(); g = g + 1 {
    for i = 0; i < v; i = i + 1 {
      for j = 0; j < v; j = j + 1 {
        let delta = if i == j { 1 } else { 0 }
        m.data[(g * v + i) * v + j] = @core.fld_sub(
          fld,
          gens[g].data[i * v + j],
          delta,
        )
      }
    }
  }
  v - @core.rank_mod(m, fld)
}

///|
/// 由「乘以 −1」的生成元建一個 1×1 矩陣。
pub fn neg_one(p : Int32) -> @core.Mat {
  let m = @core.mat_make(1, 1, 0)
  m.data[0] = p - 1
  m
}

///|
/// 恆等 1×1。
pub fn one_mat(p : Int32) -> @core.Mat {
  let m = @core.mat_make(1, 1, 0)
  m.data[0] = 1 % p
  m
}

///|
/// [T-Serre-Conv] 交叉驗證：把 Serre 譜序列的 E_∞ 總維數與獨立算出的
///   底空間胞腔複形 Betti 數比對；兩者同時「匹配」與「精確」才算收斂。
pub fn serre_matches_homology(page : @ss.Page, cx : @cellcx.CellCx) -> Bool {
  let (fit, exact) = @ss.page_converges(page, @cellcx.cx_betti_all(cx))
  fit && exact
}
