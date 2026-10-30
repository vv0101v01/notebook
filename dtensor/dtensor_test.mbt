///|
/// [T-KoszulDD][T-KoszulExact] d² = 0，且 K_* 真的是 F_2 的自由分解（H_{i≥1} = 0）。
test "Koszul complex is a resolution" {
  assert_eq(@dtensor.koszul_dd_zero(@dtensor.poly_alg(1, 4)), true)
  assert_eq(@dtensor.koszul_dd_zero(@dtensor.poly_alg(2, 3)), true)
  assert_eq(@dtensor.koszul_dd_zero(@dtensor.poly_alg(3, 3)), true)
  assert_eq(@dtensor.koszul_exact(@dtensor.poly_alg(1, 4)), true)
  assert_eq(@dtensor.koszul_exact(@dtensor.poly_alg(2, 3)), true)
  assert_eq(@dtensor.koszul_exact(@dtensor.poly_alg(3, 3)), true)
}

///|
/// [T-Tor-Poly] A = F_2[x]：Tor_*^A(F_2,F_2) = Λ(u₁,u₂)（兩個度數 1 的生成元，
///   來自兩份分解），即 dim Tor_i = C(2, i)：1, 2, 1。
///   對照：Ext_A(F_2,F_2) = F_2[u]（每個 i 一維）—— 兩者不同，見 adams 的 Koszul 測試。
test "Tor over a polynomial algebra is an exterior algebra on 2g generators" {
  let a = @dtensor.poly_alg(1, 4)
  assert_eq(@dtensor.tor_dim(a, 0, 0), 1)
  assert_eq(@dtensor.tor_dim(a, 1, 1), 2)
  assert_eq(@dtensor.tor_dim(a, 2, 2), 1)
  assert_eq(@dtensor.tor_dim(a, 3, 3), 0) // g = 1 時複形長度 2
  // 內部度數必須等於同調度
  assert_eq(@dtensor.tor_dim(a, 1, 2), 0)
  assert_eq(@dtensor.tor_total(a, 2, 2), 4)
}

///|
/// [T-Tor-Gens] g 個生成元：dim Tor_i = C(2g, i)（複形 = 2g 個生成元的外代數）。
test "Tor of a polynomial algebra on g generators" {
  let a2 = @dtensor.poly_alg(2, 4)
  assert_eq(@dtensor.tor_dim(a2, 0, 0), 1)
  assert_eq(@dtensor.tor_dim(a2, 1, 1), 4)
  assert_eq(@dtensor.tor_dim(a2, 2, 2), 6)
  assert_eq(@dtensor.tor_dim(a2, 3, 3), 4)
  assert_eq(@dtensor.tor_dim(a2, 4, 4), 1)
  let a3 = @dtensor.poly_alg(3, 4)
  assert_eq(@dtensor.tor_dim(a3, 1, 1), 6)
  assert_eq(@dtensor.tor_dim(a3, 3, 3), 20)
  assert_eq(@dtensor.tor_dim(a3, 6, 6), 1)
}

///|
/// [T-Kunneth-DTensor] 導出張量積的 Künneth 公式：
///   Tor^{A⊗B}_i = ⊕_{i₁+i₂=i} Tor^A_{i₁} ⊗ Tor^B_{i₂}，
///   即 Tor(g₁ + g₂) 是 Tor(g₁) 與 Tor(g₂) 的卷積（三張表獨立算出）。
test "Kunneth for the derived tensor product" {
  let a = @dtensor.poly_alg(1, 5)
  let b = @dtensor.poly_alg(2, 5)
  let ab = @dtensor.poly_alg(3, 5)
  assert_eq(@dtensor.koszul_dd_zero(ab), true)
  let mut ok = true
  for i = 0; i <= 3; i = i + 1 {
    for t = 0; t <= 5; t = t + 1 {
      let mut want = 0
      for i1 = 0; i1 <= i; i1 = i1 + 1 {
        for t1 = 0; t1 <= t; t1 = t1 + 1 {
          want = want +
            @dtensor.tor_dim(a, i1, t1) * @dtensor.tor_dim(b, i - i1, t - t1)
        }
      }
      if want != @dtensor.tor_dim(ab, i, t) {
        ok = false
      }
    }
  }
  assert_eq(ok, true)
}
