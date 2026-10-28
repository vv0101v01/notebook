///| sradon 測試：Radon 譜、Sherman–Morrison FBP、帶號不變性、能量恆等式。

///|
test "[S-D-RadSpec] Radon 譜：RRᵀ = nI+J ⟹ charpoly = (x−n)^{n²−1}(x−n²−n)" {
  let q = 46337
  for n = 2; n <= 7; n = n + 1 {
    if n == 2 || n == 3 || n == 5 || n == 7 {
      let r = @sradon.radon_mat(n, q)
      let pp = @sradon.npoints(n)
      let pl = @sradon.nlines(n)
      assert_eq(r.rows, pl)
      assert_eq(r.cols, pp)
      // RᵀR = nI + J（點側，pp×pp）
      let rrt = @core.mat_mul(@core.mat_transpose(r), r, q)
      let want = @core.mat_add(
        @core.mat_scale(@core.mat_identity(pp), n % q, q),
        @sradon.ones_mat(pp, q),
        q,
      )
      if !@core.mat_eq_mod(rrt, want, q) {
        assert_false(true)
      }
      // charpoly(RRᵀ)
      let cp = @spec.charpoly(rrt, q)
      let expect = @sradon.expect_rrt_charpoly(n, q)
      assert_eq(cp.length(), expect.length())
      for k = 0; k < expect.length(); k = k + 1 {
        if ((cp[k] - expect[k]) % q + q) % q != 0 {
          assert_false(true)
        }
      }
      // charpoly(RRᵀ)（線側）= xⁿ·(x−n)^{n²−1}(x−n²−n)（額外 n 個零根）
      let rtr = @core.mat_mul(r, @core.mat_transpose(r), q)
      let cp2 = @spec.charpoly(rtr, q)
      // xⁿ：n 個零後接首一係數 1
      let zero_part : Array[Int] = []
      for k = 0; k < n; k = k + 1 {
        let _ = zero_part.push(0)
      }
      let _ = zero_part.push(1)
      let expect2 = @sradon.poly_mul(zero_part, @sradon.expect_rrt_charpoly(n, q), q)
      for k = 0; k < expect2.length(); k = k + 1 {
        if ((cp2[k] - expect2[k]) % q + q) % q != 0 {
          assert_false(true)
        }
      }
    }
  }
}

///|
test "[S-T-FBP] Sherman–Morrison 濾波：精確 FBP 重構" {
  let q = 46337
  let r = @core.rng_seed(20261029)
  for n = 2; n <= 5; n = n + 1 {
    if n == 2 || n == 3 || n == 5 {
      let rad = @sradon.radon_mat(n, q)
      let pp = @sradon.npoints(n)
      let pl = @sradon.nlines(n)
      // X·(nI+J) = I（SM 公式驗證）
      let x = @sradon.sm_filter(n, pp, q)
      let rtr = @core.mat_mul(@core.mat_transpose(rad), rad, q)
      let prod = @core.mat_mul(x, rtr, q)
      if !@core.mat_eq_mod(prod, @core.mat_identity(pp), q) {
        assert_false(true)
      }
      // FBP：f̃ = X·Rᵀ·(Rf) = f
      let f = @core.mat_build(pp, 1, (_i, _j) => @core.rng_below(r, q))
      let g = @core.mat_mul(rad, f, q) // 線積分
      let rt = @core.mat_transpose(rad)
      let bp = @core.mat_mul(rt, g, q) // 反投影
      let f_hat = @core.mat_mul(x, bp, q)
      if !@core.mat_eq_mod(f_hat, f, q) {
        assert_false(true)
      }
      let _ = pl
    }
  }
}

///|
test "[S-C-GradedRad] 奇偶帶號 Radon：譜不變、帶號 FBP 仍精確" {
  let q = 46337
  let r = @core.rng_seed(1234)
  for n = 3; n <= 5; n = n + 2 {
    let rad = @sradon.radon_mat(n, q)
    let rgrad = @sradon.radon_graded(n, q)
    let pp = @sradon.npoints(n)
    // R̃ᵀR̃ = RᵀR（D² = I）
    let a = @core.mat_mul(@core.mat_transpose(rgrad), rgrad, q)
    let b = @core.mat_mul(@core.mat_transpose(rad), rad, q)
    if !@core.mat_eq_mod(a, b, q) {
      assert_false(true)
    }
    // 譜不變：charpoly 相同（在 points 側 RRᵀ 一般不同——但 R̃R̃ᵀ = D R Rᵀ D 相似於 RRᵀ）
    let cpg = @spec.charpoly(
      @core.mat_mul(rgrad, @core.mat_transpose(rgrad), q),
      q,
    )
    let cp = @spec.charpoly(@core.mat_mul(rad, @core.mat_transpose(rad), q), q)
    for k = 0; k < cp.length(); k = k + 1 {
      if ((cpg[k] - cp[k]) % q + q) % q != 0 {
        assert_false(true)
      }
    }
    // 帶號 FBP：資料也帶同樣的號（g̃ = D·g）⟹ 重構不變
    let x = @sradon.sm_filter(n, pp, q)
    let f = @core.mat_build(pp, 1, (_i, _j) => @core.rng_below(r, q))
    let g = @core.mat_mul(rad, f, q)
    // 帶號資料
    let g_signed = @core.mat_build(@sradon.nlines(n), 1, (i, _j) => {
      let dir = i / n
      let c = i % n
      if (dir + c) % 2 == 1 {
        (q - g.data[i]) % q
      } else {
        g.data[i]
      }
    })
    let bp = @core.mat_mul(@core.mat_transpose(rgrad), g_signed, q)
    let f_hat = @core.mat_mul(x, bp, q)
    if !@core.mat_eq_mod(f_hat, f, q) {
      assert_false(true)
    }
  }
}

///|
test "[S-T-RadEnergy] Parseval 型：Σ_lines (Rf)² = n·Σ_points f² + (Σf)²" {
  let q = 46337
  let r = @core.rng_seed(88)
  for n = 2; n <= 7; n = n + 1 {
    if n == 2 || n == 3 || n == 5 || n == 7 {
      let rad = @sradon.radon_mat(n, q)
      let pp = @sradon.npoints(n)
      let f = @core.mat_build(pp, 1, (_i, _j) => @core.rng_below(r, q))
      let g = @core.mat_mul(rad, f, q)
      let mut lhs = 0
      for i = 0; i < g.rows; i = i + 1 {
        lhs = (lhs + g.data[i] * g.data[i]) % q
      }
      let mut sq = 0
      let mut total = 0
      for i = 0; i < pp; i = i + 1 {
        sq = (sq + f.data[i] * f.data[i]) % q
        total = (total + f.data[i]) % q
      }
      let rhs = (n % q * sq % q + total * total) % q
      if ((lhs - rhs) % q + q) % q != 0 {
        assert_false(true)
      }
    }
  }
}
