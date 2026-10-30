///|
/// [T-Alg] 外代數的維數與結合律：Λ(x,y,z)（|x|=|y|=|z|=1）維數 [1,3,3,1]。
test "exterior algebra tables" {
  let a = @ahss.alg_wedge([1, 1, 1], 2)
  assert_eq(a.dims, [1, 3, 3, 1])
  assert_eq(@ahss.alg_check_assoc(a), true)
  assert_eq(@ahss.alg_check_unit(a), true)
  // 相乘的非零項數：x·y 有 3 對、x·(yz) 有 3 對
  let m11 = @ahss.alg_get_cup(a, 1, 1)
  let mut n11 = 0
  for v in m11.data {
    if v != 0 {
      n11 = n11 + 1
    }
  }
  // 有序對 (x,y) 與 (y,x) 各算一項 ⟹ 6
  assert_eq(n11, 6)
  let m12 = @ahss.alg_get_cup(a, 1, 2)
  let mut n12 = 0
  for v in m12.data {
    if v != 0 {
      n12 = n12 + 1
    }
  }
  assert_eq(n12, 3)
}

///|
/// [T-Alg] 張量積：Λ(x) ⊗ Λ(y,z) = Λ(x,y,z)（乘法表逐項相等）。
test "tensor of exterior algebras" {
  let a = @ahss.alg_wedge([1], 2)
  let b = @ahss.alg_wedge([1, 1], 2)
  let c = @ahss.alg_tensor(a, b)
  let d = @ahss.alg_wedge([1, 1, 1], 2)
  assert_eq(c.dims, d.dims)
  // 基的排序不同，故比較**基變換不變量**：每一塊乘法的秩 + 結合律 + 單位元
  let mut ok = true
  for i = 0; i <= 3; i = i + 1 {
    for j = 0; i + j <= 3; j = j + 1 {
      let r1 = @core.rank_mod(@ahss.alg_get_cup(c, i, j), @core.mk_field(2))
      let r2 = @core.rank_mod(@ahss.alg_get_cup(d, i, j), @core.mk_field(2))
      if r1 != r2 {
        ok = false
      }
    }
  }
  assert_eq(ok, true)
  assert_eq(@ahss.alg_check_assoc(c), true)
  assert_eq(@ahss.alg_check_unit(c), true)
  // S² × S³ 的係數環模型：Λ(x₂) ⊗ Λ(y₃) 維數 [1,0,1,1,0,1]
  let s2 = @ahss.alg_wedge([2], 2)
  let s3 = @ahss.alg_wedge([3], 2)
  let prod = @ahss.alg_tensor(s2, s3)
  assert_eq(prod.dims, [1, 0, 1, 1, 0, 1])
  assert_eq(@ahss.alg_check_assoc(prod), true)
  assert_eq(@ahss.alg_dim(prod, 5), 1)
}

///|
/// [T-Sq3] dim ≤ 5 的空間上 Sq³ = 0（不穩定性的直接推論）。
test "Sq3 vanishes below dimension 6" {
  assert_eq(@ahss.sq3_vanishes(@ahss.alg_wedge([3], 2)), true)
  assert_eq(@ahss.sq3_vanishes(@ahss.alg_wedge([1, 1, 1], 2)), true)
  assert_eq(
    @ahss.sq3_vanishes(
      @ahss.alg_tensor(@ahss.alg_wedge([2], 2), @ahss.alg_wedge([3], 2)),
    ),
    true,
  )
}

///|
/// [T-AHSS-Twist] 未扭曲 S³：d_3 = 0 ⟹ E_2 = E_∞（E_2 在 q ∈ {−2,0,2} 各一份 H^*(S³)）。
test "untwisted AHSS of S^3 collapses" {
  let a = @ahss.alg_wedge([3], 2)
  let page = @ahss.ahss_page(a, [-2, 0, 2], -2, 2)
  @ahss.ahss_set_d3(page, @ahss.ahss_zero_ops(a))
  assert_eq(@ss.page_zero_diffs(page), true)
  assert_eq(@ss.page_dd_zero(page), true)
  assert_eq(@ss.page_dim(page, 0, 2), 1) // q = 0 的 H^0
  assert_eq(@ss.page_dim(page, 3, 2), 1) // q = 0 的 H^3
  assert_eq(@ss.page_dim(page, 1, 2), 0) // S³ 無 H^1
  let e4 = @ss.page_next(page)
  assert_eq(@ss.page_total(e4, 0), 1) // 全部保留
  assert_eq(@ss.page_total(e4, 3), 1)
}

///|
/// [T-AHSS-Twist] 扭轉 S³（H = x ∈ H³）：d_3(1) = H ∪ 1 = x ⟹ 每一層 K-理論塔被殺。
test "twisted AHSS of S^3 kills the tower" {
  let a = @ahss.alg_wedge([3], 2)
  let page = @ahss.ahss_page(a, [-2, 0, 2], -2, 2)
  @ahss.ahss_set_d3(page, @ahss.ahss_twist_ops(a, 3, 0))
  assert_eq(@ahss.ops_is_zero(@ahss.ahss_twist_ops(a, 3, 0)), false)
  assert_eq(@ss.page_dd_zero(page), true)
  let e4 = @ss.page_next(page)
  // 三層塔的源（H^0）與靶（H^3）同時被消掉
  assert_eq(@ss.page_total(e4, 0), 0)
  assert_eq(@ss.page_total(e4, 3), 0)
}

///|
/// [T-AHSS-DD] T³（H = xyz ∈ H³）：d_3 只殺 1 在 H^0 的一條線，H^1、H^2 全留。
test "d3 squares to zero on the 3-torus" {
  let a = @ahss.alg_wedge([1, 1, 1], 2)
  let page = @ahss.ahss_page(a, [-2, 0, 2], -2, 2)
  @ahss.ahss_set_d3(page, @ahss.ahss_twist_ops(a, 3, 0))
  assert_eq(@ss.page_dd_zero(page), true)
  let e4 = @ss.page_next(page)
  assert_eq(@ss.page_dim(e4, 0, 2), 0) // H^0(q=0) 被殺
  assert_eq(@ss.page_dim(e4, 1, 2), 3) // H^1 不動
  assert_eq(@ss.page_dim(e4, 2, 2), 3) // H^2 不動
  assert_eq(@ss.page_dim(e4, 3, 2), 0) // H^3(q=0) 被殺
}
