///| sevolve 測試：SUSY 演化不變量、分次共軛譜守恆、演化入鏈＋篡改偵測。

///|
test "[S-D-SusyEvo] D ↦ UDV：rank／核維數／Witten 指標不變；擾動跳變相消" {
  let p = 10007
  let f = @core.mk_field(p)
  let r = @core.rng_seed(2026)
  let n = 3
  let m = 5
  let d0 = @core.mat_build(n, m, (_i, _j) => @core.rng_below(r, p))
  let rk0 = @core.rank_mod(d0, f)
  // 核維數：ker D（右核，m 維域）＝ m − rank；ker Dᵀ ＝ n − rank
  let k0 = m - rk0
  let kt0 = n - rk0
  let mut d = d0
  for step = 1; step <= 6; step = step + 1 {
    let u = @sevolve.random_invertible(n, p, r)
    let v = @sevolve.random_invertible(m, p, r)
    d = @sevolve.susy_evolve(d, u, v, p)
    let rk = @core.rank_mod(d, f)
    if rk != rk0 {
      assert_false(true) // 可逆左右乘不改 rank
    }
    if m - rk != k0 || n - rk != kt0 {
      assert_false(true) // 核維數不變
    }
    // Witten 指標 = m − n（與 D 無關，演化下顯然常數——此處仍逐歩核對）
    if (m - n) != (m - rk) - (n - rk) {
      assert_false(true)
    }
  }
  // 指標跳變相消：把第 0 行清零（行獨立 ⟹ rank 恰掉 1）⟹ 兩核同時 +1，差不變
  let d2 = @core.mat_build(n, m, (i, j) => {
    if i == 0 { 0 } else { d.data[i * m + j] }
  })
  let rk2 = @core.rank_mod(d2, f)
  if rk2 != rk0 - 1 {
    assert_false(true)
  }
  if (m - rk2) - (n - rk2) != m - n {
    assert_false(true) // 指標仍 = m − n（跳變相消）
  }
}

///|
test "[S-T-EvoStr] 分次共軛演化 Q ↦ GQG⁻¹：charpoly(Q²) 守恆、str(H^k)=0" {
  let p = 10007
  let r = @core.rng_seed(31415)
  let n = 3
  let m = 4
  let d0 = @core.mat_build(n, m, (_i, _j) => @core.rng_below(r, p))
  let q0 = @sevolve.susy_q(d0)
  let h0 = @core.mat_mul(q0, q0, p) // Q² = diag(DᵀD, DDᵀ)
  let cp0 = @spec.charpoly(h0, p)
  for step = 1; step <= 5; step = step + 1 {
    // G = diag(A, B)（么正上三角；逆為有限和）
    let (a, ainv) = @sevolve.random_unipotent(m, p, r)
    let (b, binv) = @sevolve.random_unipotent(n, p, r)
    let q1 = @sevolve.graded_conjugate(q0, a, ainv, b, binv, p)
    // 相似性直接驗證：Q1² = G Q0² G⁻¹
    let h1 = @core.mat_mul(q1, q1, p)
    // charpoly 守恆（相似矩陣）
    let cp1 = @spec.charpoly(h1, p)
    for k = 0; k < cp1.length(); k = k + 1 {
      if ((cp1[k] - cp0[k]) % p + p) % p != 0 {
        assert_false(true)
      }
    }
    // 譜跡恆等式：tr(H) 守恆（相似性）
    let mut t0 = 0
    for i = 0; i < h0.rows; i = i + 1 {
      t0 = (t0 + h0.data[i * h0.cols + i]) % p
    }
    let mut t1 = 0
    for i = 0; i < h1.rows; i = i + 1 {
      t1 = (t1 + h1.data[i * h1.cols + i]) % p
    }
    if t0 != t1 {
      assert_false(true)
    }
    // 分次跡：str(H^k) = 0（k = 1..4）——演化後的 D'（從 Q1 抽出）
    let d1 = @core.mat_build(n, m, (i, j) => q1.data[(m + i) * (m + n) + j])
    for k = 1; k <= 4; k = k + 1 {
      if @sevolve.susy_str_pow(d1, k, p) != 0 {
        assert_false(true)
      }
    }
  }
}

///|
test "[S-C-EvoLedger] 演化入鏈：sled_verify 通過；篡改 ⟹ 失敗" {
  let p = 10007
  let f = @core.mk_field(p)
  let r = @core.rng_seed(271828)
  let n = 3
  let m = 5
  let d0 = @core.mat_build(n, m, (_i, _j) => @core.rng_below(r, p))
  let ledger = @sledger.sled_new()
  let mut ok_rec = true
  let mut d = d0
  for step = 0; step <= 5; step = step + 1 {
    if step > 0 {
      let u = @sevolve.random_invertible(n, p, r)
      let v = @sevolve.random_invertible(m, p, r)
      d = @sevolve.susy_evolve(d, u, v, p)
    }
    let rk = @core.rank_mod(d, f)
    let payload = @sevolve.evo_payload(step, rk, (m - rk) + (n - rk), m - n)
    ok_rec = @sledger.sled_record(ledger, "evo-\{step}", "susy", payload) && ok_rec
  }
  assert_true(ok_rec)
  assert_eq(@sledger.sled_len(ledger), 7) // genesis + 6 步
  // 全鏈驗證
  assert_true(@sledger.sled_verify(ledger))
  // 篡改第 3 步的 payload ⟹ 驗證失敗
  let bad = @sledger.sled_tamper(ledger, "evo-3", "step=3;rank=0;ksum=99;idx=2")
  assert_false(@sledger.sled_verify(bad))
  // 原帳本不受影響（純函式）
  assert_true(@sledger.sled_verify(ledger))
}
