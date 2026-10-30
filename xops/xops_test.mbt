///|
/// [T-X-Vanish] twist 只在 dim H³ > 0 時可見。
test "twist visibility is governed by H^3" {
  assert_eq(@xops.xops_twist_visible(@ahss.alg_wedge([2], 2)), false) // S²
  assert_eq(@xops.xops_twist_visible(@ahss.alg_wedge([1], 2)), false) // S¹
  assert_eq(@xops.xops_twist_visible(@ahss.alg_wedge([3], 2)), true) // S³
  assert_eq(@xops.xops_twist_visible(@ahss.alg_wedge([1, 1, 1], 2)), true) // T³
  let s2s3 = @ahss.alg_tensor(@ahss.alg_wedge([2], 2), @ahss.alg_wedge([3], 2))
  assert_eq(@xops.xops_twist_visible(s2s3), true) // S²×S³
  // S² 上 H³ = 0 ⟹ d_3 的 twist 部分為零矩陣
  let s2 = @ahss.alg_wedge([2], 2)
  assert_eq(@ahss.ops_is_zero(@ahss.ahss_twist_ops(s2, 3, 0)), true)
}

///|
/// [T-X-Sum] 不相交並的扭曲 AHSS 可加：E_∞(X ⊔ Y) = E_∞(X) ⊕ E_∞(Y)。
test "twisted AHSS is additive on disjoint unions" {
  let s3 = @ahss.alg_wedge([3], 2)
  let s2 = @ahss.alg_wedge([2], 2)
  let sum = @xops.alg_sum(s3, s2)
  assert_eq(sum.dims, [2, 0, 1, 1])
  // 扭轉只作用在 S³ 這一份（H = H³ 的第 0 個基類）
  let psum = @ahss.ahss_page(sum, [-2, 0, 2], -2, 2)
  @ahss.ahss_set_d3(psum, @ahss.ahss_twist_ops(sum, 3, 0))
  assert_eq(@ss.page_dd_zero(psum), true)
  let esum = @ss.page_next(psum)
  // 分別算兩份
  let p3 = @ahss.ahss_page(s3, [-2, 0, 2], -2, 2)
  @ahss.ahss_set_d3(p3, @ahss.ahss_twist_ops(s3, 3, 0))
  let e3 = @ss.page_next(p3)
  let p2 = @ahss.ahss_page(s2, [-2, 0, 2], -2, 2)
  @ahss.ahss_set_d3(p2, @ahss.ahss_zero_ops(s2))
  let e2 = @ss.page_next(p2)
  let mut ok = true
  for n = 0; n <= 5; n = n + 1 {
    if @ss.page_total(esum, n) != @ss.page_total(e3, n) + @ss.page_total(e2, n) {
      ok = false
    }
  }
  assert_eq(ok, true)
}

///|
/// [T-X-Site] 非交叉森林的「分量覆蓋」是格羅滕迪克拓撲（n = 3 全驗）。
test "non-crossing forest site is a Grothendieck topology" {
  let t = @xops.xops_nc_topology(3, 2)
  assert_eq(@grotop.site_valid(t.site), true)
  assert_eq(t.site.n, 8) // 三角形有 3 條弦 ⟹ 8 個子集全非交叉
  assert_eq(@grotop.top_axiom_max(t), true)
  assert_eq(@grotop.top_axiom_pull(t), true)
  assert_eq(@grotop.top_axiom_local(t), true)
  // n = 4：只驗 (T1)、(T2)（全量驗 (T3) 成本太高）
  let t4 = @xops.xops_nc_topology(4, 2)
  assert_eq(@grotop.top_axiom_max(t4), true)
  assert_eq(@grotop.top_axiom_pull(t4), true)
  // n = 4：6 條弦中恰有一對相交 {02,13}，故非交叉子集 = 64 − 16 = 48
  assert_eq(t4.site.n, 48)
}

///|
/// [T-X-Obstruct] 局部 twist 的黏合障礙：可黏者為 0，不可黏者為正。
test "obstruction to gluing a local twist" {
  let t = @xops.xops_nc_topology(4, 2)
  // (a) 可黏：常數層 F(U) = F_p、限制為單位
  let good = @grotop.pf_new(t.site, Array::make(t.site.n, 1), fn(a, b) {
    let _ = a
    let _ = b
    Some(@core.mat_make(1, 1, 1))
  })
  assert_eq(@xops.xops_twist_obstruction(good, t), 0)
  assert_eq(@grotop.is_sheaf(good, t), true)
  // (b) 不可黏：限制為零映射（局部類之間毫無相容性）
  let bad = @grotop.pf_new(t.site, Array::make(t.site.n, 1), fn(a, b) {
    let _ = a
    let _ = b
    Some(@core.mat_make(1, 1, 0))
  })
  assert_eq(@xops.xops_twist_obstruction(bad, t) > 0, true)
  assert_eq(@grotop.is_sheaf(bad, t), false)
  // (c) 「弦上的函數」層 F(U) = F_p^{|U|}：對分量覆蓋是層（障礙 0）
  let total = @core.int_pow(2, 6)
  let idx_of : Array[Int32] = Array::make(total, -1)
  let masks : Array[Int32] = []
  for m = 0; m < total; m = m + 1 {
    if @xops.forest_noncrossing(4, m) {
      idx_of[m] = masks.length()
      masks.push(m)
    }
  }
  let dims = Array::makei(masks.length(), i => @xops.mask_popcount(masks[i]))
  let f = @grotop.pf_new(t.site, dims, fn(a, b) {
    // 投影：F(U_b) → F(U_a)，a ⊆ b
    let ma = masks[a]
    let mb = masks[b]
    let cols = @xops.mask_popcount(mb)
    let rows = @xops.mask_popcount(ma)
    let m = @core.mat_make(rows, cols, 0)
    let mut r = 0
    for i = 0; i < 6; i = i + 1 {
      if (ma >> i) % 2 == 1 {
        let mut c = 0
        for j = 0; j < 6; j = j + 1 {
          if (mb >> j) % 2 == 1 {
            if i == j {
              m.data[r * cols + c] = 1
            }
            c = c + 1
          }
        }
        r = r + 1
      }
    }
    Some(m)
  })
  assert_eq(@grotop.is_sheaf(f, t), true)
  assert_eq(@xops.xops_twist_obstruction(f, t), 0)
}

///|
/// [T-X-Koszul] Koszul 對偶：Ext_{Λ(V)}(F_2,F_2) 在 (i,i) 恆為 1；
///   Tor^{Sym(V)}_i(F_2,F_2) = C(2g, i)。兩個套件獨立算出，兩面互為見證。
test "Koszul duality: Ext of the exterior algebra vs Tor of the symmetric algebra" {
  // g = 1：Ext 每個 (i,i) = 1；Tor = 1, 2, 1
  assert_eq(@xops.xops_koszul_pair(1, 0), (1, 1))
  assert_eq(@xops.xops_koszul_pair(1, 1), (1, 2))
  assert_eq(@xops.xops_koszul_pair(1, 2), (1, 1))
  // g = 2：Ext 仍為 1；Tor = 1, 4, 6
  assert_eq(@xops.xops_koszul_pair(2, 1), (1, 4))
  assert_eq(@xops.xops_koszul_pair(2, 2), (1, 6))
}
