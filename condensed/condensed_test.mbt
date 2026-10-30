///|
/// [T-Prof] profinite 物件的合法性：滿射 + one-hot。
test "profinite presentation is valid" {
  assert_eq(@condensed.prof_valid(@condensed.prof_zp(3, 2)), true)
  assert_eq(@condensed.prof_valid(@condensed.prof_cantor(3, 2)), true)
  assert_eq(@condensed.prof_valid(@condensed.prof_ninf(4, 3)), true)
  let pr = @condensed.prof_prod(
    @condensed.prof_zp(2, 2),
    @condensed.prof_zp(2, 3),
  )
  assert_eq(@condensed.prof_valid(pr), true)
  assert_eq(pr.sizes, [6, 36])
}

///|
/// [T-ExtVan] 自由凝聚群與函數鏈的 Mittag-Leffler 證書 ⟹ Ext^{i>0} = 0。
test "solid Ext vanishes in positive degrees" {
  let cases = [
    @condensed.prof_zp(3, 2),
    @condensed.prof_cantor(3, 2),
    @condensed.prof_ninf(4, 3),
    @condensed.prof_prod(@condensed.prof_zp(2, 2), @condensed.prof_zp(2, 3)),
  ]
  let mut ok = true
  for pr in cases {
    if !@condensed.cond_ext_vanishes(pr, 2) {
      ok = false
    }
  }
  assert_eq(ok, true)
}

///|
/// [T-Solid] F_p 非固態：Hom(Z[S]^■,F_p) = 全部局部常數函數（大），
///   而 Hom(Z[S],F_p) 只有「常數」型（小）；缺口 = k(|S_N| − |S_0|) > 0。
test "F_p is not solid: the solidity defect is positive" {
  let zp = @condensed.prof_zp(3, 2)
  // Z_2 的層級 0 是 Z/2（2 個點）⟹ 只有常數型映射，維數 2
  assert_eq(@condensed.cond_hom_free_discrete(zp, 1), 2)
  assert_eq(@condensed.cond_hom_solid_discrete(zp, 1), 8) // 8 個局部常數函數
  assert_eq(@condensed.cond_solidity_defect(zp, 1), 6)
  // 單點：缺口 0
  assert_eq(@condensed.cond_solidity_defect(@condensed.prof_pt(2), 1), 0)
  // 多維係數
  assert_eq(@condensed.cond_hom_free_discrete(zp, 3), 6)
  assert_eq(@condensed.cond_hom_solid_discrete(zp, 3), 24)
  // 兩點集：層級 0 已含兩點 ⟹ 兩邊都 2 維（此例缺口 0）
  let two = @condensed.prof_new(
    [2, 4],
    [@core.mat_from_rows([[1, 0, 0, 1], [0, 1, 1, 0]])],
    2,
  )
  assert_eq(@condensed.prof_valid(two), true)
  assert_eq(@condensed.cond_hom_free_discrete(two, 1), 2)
}

///|
/// [T-SolidCompact] 緊目標 Z_p 固態：兩邊都是 lim_n (Z/p^n)^{|S_0|}，缺口為 0。
test "profinite targets are solid" {
  let zp = @condensed.prof_zp(3, 2)
  assert_eq(@condensed.cond_solidity_defect_profinite(zp, 1), 0)
  let cantor = @condensed.prof_cantor(3, 2)
  assert_eq(@condensed.cond_solidity_defect_profinite(cantor, 1), 0)
  assert_eq(@condensed.cond_solidity_defect_profinite(cantor, 2), 0)
}

///|
/// [T-Tensor] Z[S]^■ ⊗ Z[T]^■ ≅ Z[S×T]^■：逐層矩陣相等。
test "tensor of free solid groups is free on the product" {
  let a = @condensed.prof_zp(2, 2)
  let b = @condensed.prof_zp(2, 3)
  let lhs = @condensed.chain_tensor(
    @condensed.chain_free(a),
    @condensed.chain_free(b),
  )
  let rhs = @condensed.chain_free(@condensed.prof_prod(a, b))
  assert_eq(@condensed.chain_eq(lhs, rhs), true)
  // 也對 {0,1}^n 成立
  let c = @condensed.prof_cantor(2, 2)
  let d = @condensed.prof_ninf(3, 2)
  let lhs2 = @condensed.chain_tensor(
    @condensed.chain_free(c),
    @condensed.chain_free(d),
  )
  let rhs2 = @condensed.chain_free(@condensed.prof_prod(c, d))
  assert_eq(@condensed.chain_eq(lhs2, rhs2), true)
  // 極限維數 = 乘積層級 0 的維數（cantor 層級 0 有 2 點）
  assert_eq(@condensed.chain_lim_dim(rhs2), 2)
}
