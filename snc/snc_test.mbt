///| snc 測試：NC 格的計數與 Möbius「超維數」、自由累積量、von Szily 交錯和、flip 圖譜。

///|
test "[S-D-NCPart] |NC(n)| = Catalan(n)（n ≤ 7 枚舉驗證）" {
  // Catalan: 1, 1, 2, 5, 14, 42, 132, 429
  let expect = [1, 1, 2, 5, 14, 42, 132, 429]
  for n = 1; n <= 7; n = n + 1 {
    let ncs = @snc.nc_partitions(n)
    assert_eq(ncs.length(), expect[n])
    assert_eq(@snc.catalan(n), expect[n])
  }
  // 對照：全部分割數（Bell）：Bell(4) = 15 > |NC(4)| = 14（唯一交叉者：{13}{24} 型）
  let all4 = @snc.all_partitions(4)
  assert_eq(all4.length(), 15)
  let ncs4 = @snc.nc_partitions(4)
  assert_eq(ncs4.length(), 14)
}

///|
test "[S-T-MobiusNC] Kreweras 超積公式：μ(0̂,π) = ∏_B (−1)^{|B|−1}C_{|B|−1}" {
  let n = 6
  let ncs = @snc.nc_partitions(n)
  let mu = @snc.mobius_from_bottom(n)
  let key = fn(b : Array[Int]) -> Int {
    let mut k = 0
    for x in b {
      k = k * 10 + x + 1
    }
    k
  }
  let mut checked = 0
  for part in ncs {
    let mut prod = 1
    for block in @snc.block_list(part) {
      let sz = block.length()
      let m = @snc.catalan(sz - 1)
      if sz % 2 == 0 {
        prod = -prod * m
      } else {
        prod = prod * m
      }
    }
    let got = mu.get(key(part))
    assert_true(got is Some(v) && v == prod)
    checked = checked + 1
  }
  assert_eq(checked, 132) // NC(6)
  // 頂端：μ(0̂,1̂) = (−1)^5 C_5 = −42
  let top : Array[Int] = [0, 0, 0, 0, 0, 0]
  let got = mu.get(key(top))
  assert_true(got is Some(v) && v == -42)
}

///|
test "[S-D-FreeCum] 自由累積量 ⟷ 矩：MP（r≡1）與半圓律（r=e₂）" {
  let p = 46337
  // (1) r ≡ 1：m_n = |NC(n)| = Catalan(n)（Marchenko–Pastur 秩 1）
  for n = 1; n <= 6; n = n + 1 {
    let r : Array[Int] = Array::make(n + 1, 1)
    let m = @snc.moment_from_free_cumulants(r, n, p)
    assert_eq(m, @snc.catalan(n))
  }
  // (2) r = e₂（r[2] = 1 其餘 0）：半圓律 m_{2k} = C_k、奇矩 = 0
  for n = 1; n <= 6; n = n + 1 {
    let r : Array[Int] = Array::make(n + 1, 0)
    if n >= 2 {
      r[2] = 1
    }
    let m = @snc.moment_from_free_cumulants(r, n, p)
    if n % 2 == 1 {
      assert_eq(m, 0)
    } else {
      assert_eq(m, @snc.catalan(n / 2))
    }
  }
}

///|
test "[S-D-vonSzily] 超卡特蘭：閉式 = von Szily 交錯和（m,n ≤ 6）" {
  let p = 46337
  let mut ok = true
  for m = 0; m <= 6; m = m + 1 {
    for n = m + 1; n <= 6; n = n + 1 {
      // 只測 n > m（對稱性之外的三角帶即可；S(m,n) = S(n,m) 由公式對稱）
      let closed = @snc.super_catalan(m, n, p)
      let sum = @snc.von_szily_sum(m, n, p)
      if closed != sum {
        ok = false
      }
    }
  }
  assert_true(ok)
  // 具體值（Gessel 整數正規化）：S(1,n) = 2·C_n；S(2,2) = 6；S(2,3) = 12
  assert_eq(@snc.super_catalan(1, 5, p), 84)
  assert_eq(@snc.super_catalan(1, 5, p), 2 * @snc.catalan(5))
  assert_eq(@snc.super_catalan(2, 2, p), 6)
  assert_eq(@snc.super_catalan(2, 3, p), 12)
  // S(m,1) = S(1,m)（對稱）
  assert_eq(@snc.super_catalan(5, 1, p), @snc.super_catalan(1, 5, p))
}

///|
test "[S-D-FlipSpec] flip 圖：五邊形 ≅ C₅（譜相同）；直徑與正則性（N=4..8）" {
  let p = 10007
  // 五邊形 flip 圖 ≅ C₅
  let (v5, adj5) = @snc.flip_graph(5, p)
  assert_eq(v5, 5)
  let cp_flip = @spec.charpoly(adj5, p)
  let c5 = @snc.cycle_adj(5, p)
  let cp_cycle = @spec.charpoly(c5, p)
  for k = 0; k <= 5; k = k + 1 {
    assert_eq(cp_flip[k], cp_cycle[k])
  }
  // 譜恆等式：tr(A) = 0（無自環）、tr(A²) = 2·邊數
  let mut tr = 0
  for i = 0; i < v5; i = i + 1 {
    tr = (tr + adj5.data[i * v5 + i]) % p
  }
  assert_eq(tr, 0)
  let mut tr2 = 0
  for i = 0; i < v5; i = i + 1 {
    for j = 0; j < v5; j = j + 1 {
      tr2 = (tr2 + adj5.data[i * v5 + j] * adj5.data[j * v5 + i]) % p
    }
  }
  assert_eq(tr2, 10) // 2 × 5 條邊
  // 直徑與頂點數：N=4..8
  let diam_expect = [0, 0, 0, 0, 1, 2, 4, 5, 7] // diam_expect[N]
  let catalan_expect = [0, 0, 0, 1, 2, 5, 14, 42, 132]
  for n = 4; n <= 8; n = n + 1 {
    let (v, adj) = @snc.flip_graph(n, p)
    assert_eq(v, catalan_expect[n]) // Catalan(N−2)
    // (N−3)-正則
    let mut reg = true
    for i = 0; i < v; i = i + 1 {
      let mut deg = 0
      for j = 0; j < v; j = j + 1 {
        deg = deg + adj.data[i * v + j]
      }
      if deg != n - 3 {
        reg = false
      }
    }
    assert_true(reg)
    let diam = @snc.graph_diameter(v, adj)
    assert_eq(diam, diam_expect[n])
  }
}
