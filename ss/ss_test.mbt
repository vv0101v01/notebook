///|
/// [T-SS-Cancel] 1×1 的非零 d_r 會同時消掉源與靶兩個胞腔。
test "a 1x1 differential kills both cells" {
  // 標準型 d_2: (p,q) → (p+2, q−1)，故源在索引 (0,1)、靶在 (2,0)
  let page = @ss.page_new(2, 0, 0, 3, 3, 7)
  @ss.page_setdim(page, 0, 1, 1)
  @ss.page_setdim(page, 2, 0, 1)
  @ss.page_setd(page, 0, 1, @core.mat_from_rows([[1]]))
  assert_eq(@ss.page_dd_zero(page), true)
  assert_eq(@ss.page_dim(page, 0, 1), 1)
  assert_eq(@ss.page_dim(page, 2, 0), 1)
  let next = @ss.page_next(page)
  assert_eq(@ss.page_dim(next, 0, 1), 0)
  assert_eq(@ss.page_dim(next, 2, 0), 0)
  assert_eq(next.r, 3)
}

///|
/// [T-SS-Boundary] 單一胞腔時同調就是它自己（核 = 像 = 0）。
test "isolated cell survives every page" {
  let page = @ss.page_new(2, 0, 0, 2, 2, 5)
  @ss.page_setdim(page, 1, 1, 1)
  assert_eq(@ss.page_zero_diffs(page), true)
  assert_eq(@ss.page_ker_dim(page, 1, 1), 1)
  assert_eq(@ss.page_im_dim(page, 1, 1), 0)
  assert_eq(@ss.page_hom_dim(page, 1, 1), 1)
}

///|
/// [T-SS-DD] 全零微分的頁 `page_dd_zero` = true，且總維數保守。
test "totals are preserved by page_next" {
  let page = @ss.page_new(1, 0, 0, 3, 3, 3)
  @ss.page_setdim(page, 0, 0, 2)
  @ss.page_setdim(page, 2, 2, 3)
  let t_before = @ss.page_total(page, 0) +
    @ss.page_total(page, 1) +
    @ss.page_total(page, 2)
  let next = @ss.page_next(page)
  let t_after = @ss.page_total(next, 0) +
    @ss.page_total(next, 1) +
    @ss.page_total(next, 2)
  assert_eq(t_before, t_after)
}

///|
/// [T-SS-Tensor] 張量頁：維數相乘、座標相加。
test "tensor of pages" {
  let a = @ss.page_new(2, 0, 0, 2, 2, 2)
  @ss.page_setdim(a, 0, 0, 1)
  @ss.page_setdim(a, 1, 1, 1)
  let b = @ss.page_new(2, 0, 0, 2, 2, 2)
  @ss.page_setdim(b, 1, 0, 1)
  let c = @ss.page_tensor(a, b)
  // (0,0)+(1,0) = (1,0)； (1,1)+(1,0) = (2,1)
  assert_eq(@ss.page_dim(c, 1, 0), 1)
  assert_eq(@ss.page_dim(c, 2, 1), 1)
  assert_eq(@ss.page_support(c), 2)
}

///|
/// [T-SS-Flip] q 方向翻轉：Adams 型的 d_r 目標是 (p+r, q+r−1)。
test "qflip changes the differential target" {
  let standard = @ss.page_new(2, 0, 0, 3, 3, 2)
  assert_eq(@ss.page_target_q(standard, 1), 0)
  let adams = @ss.page_new_q(2, 0, 0, 3, 3, 2, true)
  assert_eq(@ss.page_target_q(adams, 1), 2)
  assert_eq(@ss.page_source_q(adams, 2), 1)
}
