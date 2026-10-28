///| smetric 測試：環圖 Laplacian 譜、mod-p 零維數、同譜不同構、VR 條碼、Hodge。

///|
test "[S-D-CycLap] 環圖 Laplacian 譜：0 單根、tr=2n、tr(L²)=6n、λ_max=4" {
  // 整數層面（mod p）
  let p = 10007
  for n = 4; n <= 10; n = n + 1 {
    let l = @smetric.cycle_lap(n, p)
    let cp = @spec.charpoly(l, p)
    // 連通 ⟹ 0 是單根
    assert_eq(@spec.root_zero_mult(cp), 1)
    // tr L = 2n
    let mut tr = 0
    for i = 0; i < n; i = i + 1 {
      tr = (tr + l.data[i * n + i]) % p
    }
    assert_eq(tr, 2 * n % p)
    // tr L² = 6n
    let l2 = @core.mat_mul(l, l, p)
    let mut tr2 = 0
    for i = 0; i < n; i = i + 1 {
      tr2 = (tr2 + l2.data[i * n + i]) % p
    }
    assert_eq(tr2, 6 * n % p)
  }
  // 浮點層面：偶 n 的 λ_max = 4（k = n/2：2−2cos π）；不同特徵值數
  for n = 4; n <= 10; n = n + 2 {
    let ld : Array[Array[Double]] = []
    for i = 0; i < n; i = i + 1 {
      let row : Array[Double] = Array::make(n, 0.0)
      for j = 0; j < n; j = j + 1 {
        if j == (i + 1) % n || j == (i + n - 1) % n {
          row[j] = -1.0
        }
      }
      row[i] = 2.0
      let _ = ld.push(row)
    }
    let (vals, _) = @spec.jacobi_eigen(ld)
    // 排序後最大
    let vmax = vals[vals.length() - 1]
    if (vmax - 4.0).abs() > 0.000001 {
      assert_false(true)
    }
    // 不同特徵值個數 = n/2 + 1（λ_k = λ_{n−k}）
    let mut distinct = 0
    let mut i = 0
    while i < vals.length() {
      let mut j = i
      while j + 1 < vals.length() && (vals[j + 1] - vals[i]).abs() < 0.000001 {
        j = j + 1
      }
      distinct = distinct + 1
      i = j + 1
    }
    assert_eq(distinct, n / 2 + 1)
  }
}

///|
test "[S-T-LapNullity] mod-p 零維數：nullity L(C_n) = 1 + [p | n]" {
  let ps = [5, 7, 11]
  for p in ps {
    for n = 4; n <= 10; n = n + 1 {
      let l = @smetric.cycle_lap(n, p)
      let nu = @smetric.nullity_mod(l, p)
      let expect = if n % p == 0 { 2 } else { 1 }
      assert_eq(nu, expect)
    }
  }
  // 解的形狀驗證（n = 5, p = 5）：v_i = α + βi 型二維零空間
  let p = 5
  let l = @smetric.cycle_lap(5, p)
  let f = @core.mk_field(p)
  let ns = @core.nullspace_basis(l, f)
  assert_eq(ns.length(), 2)
}

///|
test "[S-NEG-Cospectral] K_{1,4} 與 C₄∪K₁ 同譜不同構（譜不決定度量）" {
  let p = 10007
  let s = @smetric.star_adj(p)
  let c = @smetric.c4_plus_iso_adj(p)
  let cps = @spec.charpoly(s, p)
  let cpc = @spec.charpoly(c, p)
  // 同譜：charpoly 相同（特徵值 {2, −2, 0, 0, 0}）
  assert_eq(cps.length(), cpc.length())
  for k = 0; k < cps.length(); k = k + 1 {
    if ((cps[k] - cpc[k]) % p + p) % p != 0 {
      assert_false(true)
    }
  }
  // 顯式核對特徵值多項式 = x³(x−2)(x+2) = x⁵ − 4x³
  assert_eq(((cps[0] % p) + p) % p, 0)
  assert_eq(((cps[1] % p) + p) % p, 0)
  assert_eq(((cps[2] % p) + p) % p, 0)
  assert_eq(((cps[3] % p) + p) % p, (p - 4) % p)
  assert_eq(cps[4], 0)
  assert_eq(cps[5], 1)
  // 但不同構：度序列不同（(4,1,1,1,1) vs (2,2,2,2,0)）
  let degs = fn(a : @core.Mat) -> Array[Int] {
    let out : Array[Int] = []
    for i = 0; i < a.rows; i = i + 1 {
      let mut d = 0
      for j = 0; j < a.cols; j = j + 1 {
        d = d + a.data[i * a.cols + j]
      }
      let _ = out.push(d)
    }
    // 排序
    let o = out
    for i = 1; i < o.length(); i = i + 1 {
      let mut j = i
      while j > 0 && o[j - 1] > o[j] {
        let t = o[j - 1]
        o[j - 1] = o[j]
        o[j] = t
        j = j - 1
      }
    }
    o
  }
  let ds = degs(s)
  let dc = degs(c)
  let mut same = true
  for i = 0; i < 5; i = i + 1 {
    if ds[i] != dc[i] {
      same = false
    }
  }
  assert_false(same) // ⟹ 譜相同但圖不同構
  // 度量層面：星圖連通（diam 2）、C₄∪K₁ 不連通——譜看不見連通性
  let mut connected_s = true
  for j = 1; j < 5; j = j + 1 {
    if s.data[j] == 0 {
      connected_s = false
    }
  }
  assert_true(connected_s)
  if c.data[4] != 0 || c.data[4 * 5] != 0 {
    assert_false(true) // K₁ 孤立
  }
}

///|
test "[S-D-VRBar] VR 條碼：r=0 ⟹ (n,0)；r=1 ⟹ (1,1)（圓圈誕生）χ=0" {
  for n = 4; n <= 8; n = n + 1 {
    let m = @metric.mspace_cycle(n, 1)
    let b0 = @metric.vr_betti_all(m, 0)
    assert_eq(b0[0], n)
    let b1 = @metric.vr_betti_all(m, 1)
    assert_eq(b1[0], 1)
    assert_eq(b1[1], 1)
    // Euler 特徵 = β₀ − β₁ = 0（圓圈）
    assert_eq(@metric.alt_sum(b1), 0)
  }
}

///|
test "[S-D-Hodge] Hodge β₁ = VR β₁（獨立計算對照；n=4..8、r=1,2）" {
  let p = 10007
  for n = 4; n <= 8; n = n + 1 {
    let m = @metric.mspace_cycle(n, 1)
    for r = 1; r <= 2; r = r + 1 {
      let hb = @smetric.hodge_beta1(m, r, p)
      if hb is Some(h) {
        let b = @metric.vr_betti_all(m, r)
        if b.length() > 1 {
          if h != b[1] {
            assert_false(true)
          }
        }
      } else {
        assert_false(true)
      }
    }
  }
  // C₄ 在 r=2：VR = K₄（可單純收縮）⟹ β₁ = 0
  let m4 = @metric.mspace_cycle(4, 1)
  let hb4 = @smetric.hodge_beta1(m4, 2, p)
  if hb4 is Some(h) {
    assert_eq(h, 0)
  } else {
    assert_false(true)
  }
}
