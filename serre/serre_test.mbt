///|
/// [T-Serre-Hopf] Hopf 纖維化：E^2 有 4 個非零格，d_2 是 Euler 類的同構，
///   E_∞ 只在總次數 0、3 ⟹ 完全匹配獨立算出的 H_*(S^3)（@cellcx）。
test "Serre spectral sequence of the Hopf fibration" {
  let e2 = @serre.hopf(1, 7)
  assert_eq(@ss.page_dd_zero(e2), true)
  assert_eq(@ss.page_support(e2), 4)
  assert_eq(@ss.page_total(e2, 0), 1)
  assert_eq(@ss.page_total(e2, 3), 1)
  // d_2 非零 ⟹ 取下一頁
  let e3 = @ss.page_next(e2)
  assert_eq(@ss.page_zero_diffs(e3), true)
  assert_eq(@ss.page_total(e3, 0), 1)
  assert_eq(@ss.page_total(e3, 1), 0)
  assert_eq(@ss.page_total(e3, 2), 0)
  assert_eq(@ss.page_total(e3, 3), 1)
  // 與 cellcx 的 H_*(S^3) 交叉驗證
  let s3 = @cellcx.cx_sphere(3, 7)
  let target = @cellcx.cx_betti_all(s3)
  let _ = target
  assert_eq(target, [1, 0, 0, 1])
  assert_eq(@serre.serre_sphere_converges(1, 1, 7), true)
}

///|
/// [T-Serre-Bundle] 球叢 S^n → S^{2n+1} → S^{n+1}：n = 1, 2, 3 都收斂到 S^{2n+1}；
///   而 Euler 數 e = 0（平凡積）時 E_∞ 是 S^n × S^{n+1} 的同調（不可能是球面）。
test "Serre spectral sequence of sphere bundles" {
  for n in [1, 2, 3] {
    assert_eq(@serre.serre_sphere_converges(n, 1, 11), true)
    assert_eq(@serre.serre_sphere_converges(n, 2, 11), true)
  }
  // e = 0：微分為零 ⟹ E_∞ = E^2 = H_*(S^{n+1}) ⊗ H_*(S^n)
  let flat = @serre.sphere_bundle(2, 0, 11)
  assert_eq(@ss.page_zero_diffs(flat), true)
  assert_eq(@ss.page_total(flat, 3), 1) // (2,0)⊗… 的 (3,0)? 見下：總次數 3 只有 (3,0)
  assert_eq(@ss.page_total(flat, 5), 1) // (3,2) 的總次數 5
  // 對照：e ≠ 0 時總次數 2、3 被殺掉
  let twisted = @serre.sphere_bundle(2, 1, 11)
  let fin = @serre.serre_run(twisted, 4)
  assert_eq(@ss.page_total(fin, 2), 0)
  assert_eq(@ss.page_total(fin, 5), 1)
}

///|
/// [T-Serre-Deg] 兩列譜序列的邊緣退化：S^2 × S^3 的「乘積譜序列」不需跑微分。
test "degenerate two-column page" {
  let bb = @serre.sphere_betti(2)
  let bf = @serre.sphere_betti(3)
  let e2 = @serre.serre_e2(bb, bf, 7)
  assert_eq(@serre.serre_degenerate_two_columns(e2), true)
  assert_eq(@ss.page_zero_diffs(e2), true)
  assert_eq(@ss.page_support(e2), 4)
  // E_∞ 的總維數 = Künneth：H_*(S^2×S^3) = 1,0,1,1,0,1
  let prod = @cellcx.cx_product(
    @cellcx.cx_sphere(2, 7),
    @cellcx.cx_sphere(3, 7),
  )
  assert_eq(@cellcx.cx_betti_all(prod), [1, 0, 1, 1, 0, 1])
  assert_eq(@ss.page_converges(e2, @cellcx.cx_betti_all(prod)), (true, true))
}

///|
/// [T-Serre-Twist] 扭轉係數：g = −1 作用在 1 維空間上。
///   p = 2 時 −1 = 1 ⟹ 不變量 = 餘不變量 = 1；p = 7 時 −1 ≠ 1 ⟹ 兩者皆 0。
test "twisted coefficients: invariants and coinvariants" {
  let g2 = [@serre.neg_one(2)]
  assert_eq(@serre.invariants_dim(1, g2, 2), 1)
  assert_eq(@serre.coinvariants_dim(1, g2, 2), 1)
  let g7 = [@serre.neg_one(7)]
  assert_eq(@serre.invariants_dim(1, g7, 7), 0)
  assert_eq(@serre.coinvariants_dim(1, g7, 7), 0)
  // 平凡作用：兩種都等於原維數
  assert_eq(@serre.invariants_dim(3, [], 7), 3)
  assert_eq(@serre.coinvariants_dim(3, [], 7), 3)
  // V = F_7^2，g = diag(1,−1)：不變量 1 維、餘不變量 1 維
  let d = @core.mat_make(2, 2, 0)
  d.data[0] = 1
  d.data[3] = 6
  assert_eq(@serre.invariants_dim(2, [d], 7), 1)
  assert_eq(@serre.coinvariants_dim(2, [d], 7), 1)
}
