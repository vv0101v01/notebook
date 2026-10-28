///| stwist 測試：奇偶同態與號閉鏈、H² 非平凡、Betti 譜、超中心、超特徵標。

///|
test "[S-D-Parity] 奇偶是同態；Koszul 號 σ 是 2-閉鏈" {
  // G = (ℤ/2)³：窮舉驗證 p(a+b) = p(a)+p(b) 與 σ 的閉鏈條件
  let g = @twist.grp([2, 2, 2])
  let n = @twist.grp_order(g)
  let mut ok_hom = true
  let mut ok_coc = true
  let mut a = 0
  while a < n {
    let mut b = 0
    while b < n {
      let ab = @twist.grp_code(
        g,
        @twist.grp_add(g, @twist.grp_of_code(g, a), @twist.grp_of_code(g, b)),
      )
      if (@stwist.parity(g, ab) != (@stwist.parity(g, a) + @stwist.parity(g, b)) % 2) {
        ok_hom = false
      }
      let mut c = 0
      while c < n {
        if !@stwist.sign_cocycle_holds(g, a, b, c) {
          ok_coc = false
        }
        c = c + 1
      }
      b = b + 1
    }
    a = a + 1
  }
  assert_true(ok_hom)
  assert_true(ok_coc)
  // 偶元素恰半：|p^{-1}(0)| = 2^{d−1}
  let mut even = 0
  let mut i = 0
  while i < n {
    if @stwist.parity(g, i) == 0 {
      even = even + 1
    }
    i = i + 1
  }
  assert_eq(even, 4)
}

///|
test "[S-T-SignClass] Koszul 號 σ 在 H²(G, 𝔽₂) 非平凡（d ≤ 3 窮舉）" {
  for d = 1; d <= 3; d = d + 1 {
    let orders : Array[Int] = []
    for i = 0; i < d; i = i + 1 {
      let _ = orders.push(2)
    }
    let g = @twist.grp(orders)
    // δμ = σ 無解（2^{|G|} 窮舉）
    assert_false(@stwist.sign_is_coboundary(g))
  }
  // 對照：零餘閉鏈是餘邊界（μ ≡ 0 給出 δμ = 0）
  let g1 = @twist.grp([2, 2])
  assert_true(@stwist.sign_is_coboundary_zero(g1))
}

///|
test "[S-C-H2Betti] Betti 譜：dim H^k((ℤ/2)^d, 𝔽₂) = C(d+k−1, k)" {
  // H¹ = d、H² = C(d+1,2)；H³（僅 d ≤ 2）= C(d+2,3)
  for d = 1; d <= 3; d = d + 1 {
    let orders : Array[Int] = []
    for i = 0; i < d; i = i + 1 {
      let _ = orders.push(2)
    }
    let g = @twist.grp(orders)
    let h1 = @twist.h1_dim(g, 2)
    let h2 = @twist.h2_dim(g, 2)
    assert_eq(h1, d)
    assert_eq(h2, (d + 1) * d / 2)
    if d <= 2 {
      let h3 = @stwist.h3_dim(g, 2)
      assert_eq(h3, (d + 2) * (d + 1) * d / 6)
    }
  }
}

///|
test "[S-T-SCenter] 號代數：交換（中心=全空間）但不超交換（超中心=偶部）" {
  for d = 1; d <= 3; d = d + 1 {
    let orders : Array[Int] = []
    for i = 0; i < d; i = i + 1 {
      let _ = orders.push(2)
    }
    let g = @twist.grp(orders)
    let n = @twist.grp_order(g)
    // ω = 0（平凡扭曲）＋ Koszul 號
    let s = @stwist.sw_of(g, 2, 101, Array::make(n * n, 0))
    assert_true(@stwist.sw_is_cocycle(s))
    // 普通中心 = |G|（代數交換）
    assert_eq(@stwist.sw_center_dim(s, false), n)
    // 超中心 = 偶部（d ≥ 1 時奇元素存在）
    assert_eq(@stwist.sw_center_dim(s, true), n / 2)
  }
}

///|
test "[S-NEG-OddSuperCenter] 奇超中心元素不存在：超中心 = rad ∩ 偶（一般餘閉鏈）" {
  // 定理（本實作推導）：G = (ℤ/2)^d、ℓ = 2、奇偶分次下，
  //   奇 a 超中心 ⟺ b_ω(a,·) = p；
  //   而 b_ω 是交錯雙線性形式 A，且 xᵀAx = 0 (mod 2) ⟹ Ax = 1 的解必為偶
  //   ⟹ 奇超中心元素【永遠】不存在。
  // 天真的「超中心 = 中心」也一并否決（rad 的奇元素不在超中心）。
  let r = @core.rng_seed(4242)
  let p = 101
  let mut ok = true
  let mut odd_seen = false
  for trial = 0; trial < 14; trial = trial + 1 {
    let d = 1 + @core.rng_below(r, 3)
    let orders : Array[Int] = []
    for i = 0; i < d; i = i + 1 {
      let _ = orders.push(2)
    }
    let g = @twist.grp(orders)
    let n = @twist.grp_order(g)
    let c : Array[Array[Int]] = []
    for i = 0; i < d; i = i + 1 {
      let row : Array[Int] = []
      for j = 0; j < d; j = j + 1 {
        let _ = row.push(@core.rng_below(r, 2))
      }
      let _ = c.push(row)
    }
    let s0 = @stwist.bilinear_cocycle(g, 2, p, c)
    assert_true(@stwist.sw_is_cocycle(s0))
    // 加上隨機 coboundary 擾動（仍同一上同調類；b_ω 不變）
    let mu : Array[Int] = []
    for i = 0; i < n; i = i + 1 {
      let _ = mu.push(@core.rng_below(r, 2))
    }
    let s = @stwist.sw_gauge(s0, mu)
    assert_true(@stwist.sw_is_cocycle(s))
    assert_true(@stwist.b_omega_bilinear(s))
    // 中心 = rad
    let z = @stwist.sw_center_dim(s, false)
    let rad = @stwist.sw_radical_size(s)
    if z != rad {
      ok = false
    }
    // 超中心：= |rad ∩ 偶|；奇超中心元素 = 0
    let sz = @stwist.sw_center_dim(s, true)
    let mut evencount = 0
    let mut oddcount = 0
    let mut a = 0
    while a < n {
      if @stwist.sw_supercentral(s, a) {
        if @stwist.parity(g, a) == 0 {
          evencount = evencount + 1
        } else {
          oddcount = oddcount + 1
        }
      }
      a = a + 1
    }
    if sz != evencount + oddcount || oddcount != 0 {
      ok = false
    }
    if oddcount > 0 {
      odd_seen = true
    }
    // rad 的奇元素確實不在超中心（d ≥ 1 且 rad 含奇元素時）
    // —— 由 oddcount = 0 自動成立。
  }
  assert_true(ok)
  assert_false(odd_seen) // 奇超中心元素在全部 trial 中從未出現
}

///|
test "[S-C-GrTrace] 分次正則表示：超特徵標恆 0，普通特徵標 = |G|·δ_{a,0}" {
  let g = @twist.grp([2, 2, 2])
  let n = @twist.grp_order(g)
  let p = 101
  let r = @core.rng_seed(777)
  // 隨機雙線性 ω + Koszul 號
  let c : Array[Array[Int]] = []
  for i = 0; i < 3; i = i + 1 {
    let row : Array[Int] = []
    for j = 0; j < 3; j = j + 1 {
      let _ = row.push(@core.rng_below(r, 2))
    }
    let _ = c.push(row)
  }
  let s = @stwist.bilinear_cocycle(g, 2, p, c)
  assert_true(@stwist.sw_is_cocycle(s))
  let mut all_zero = true
  let mut a = 0
  while a < n {
    if @stwist.sw_reg_trace(s, a, true) != 0 {
      all_zero = false
    }
    // 普通跡
    let tr = @stwist.sw_reg_trace(s, a, false)
    if a == 0 {
      assert_eq(tr, n % p)
    } else {
      assert_eq(tr, 0)
    }
    a = a + 1
  }
  assert_true(all_zero)
  // 對照：去掉 Koszul 號（純 ω）後超特徵標【不】恆為零？
  // 偶仍可能全消（sdim = 0）——這本身是 Witten 指標敘述：
  // |G| 偶且奇偶各半 ⟹ str(Id) = 0。此處僅聲明帶號版本。
}
