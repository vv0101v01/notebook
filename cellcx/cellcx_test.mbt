///|
/// [T-Cell-Betti][T-Cell-Euler] 球面、透鏡空間、環面的 Betti 數與 Euler 特徵。
test "betti numbers and euler characteristic" {
  for n in [0, 1, 3, 5] {
    let s = @cellcx.cx_sphere(n, 7)
    assert_eq(@cellcx.cx_check_dd(s), true)
    assert_eq(@cellcx.cx_is_sphere(s, n), true)
    assert_eq(@cellcx.cx_euler(s), @cellcx.cx_euler_betti(s))
  }
  let t2 = @cellcx.cx_torus(2, 7)
  assert_eq(@cellcx.cx_check_dd(t2), true)
  assert_eq(@cellcx.cx_betti_all(t2), [1, 2, 1])
  assert_eq(@cellcx.cx_euler(t2), 0)
  let t3 = @cellcx.cx_torus(3, 11)
  assert_eq(@cellcx.cx_betti_all(t3), [1, 3, 3, 1])
}

///|
/// [E-IntHom] 透鏡空間 L(k,1) 的整係數同調：H_0 = Z、H_1 = Z/k、H_3 = Z。
test "integer homology of lens spaces has torsion" {
  let l = @cellcx.cx_lens(5, 1, 7)
  let h = @cellcx.cx_homology_int(l)
  assert_eq(h[0].0, 1)
  assert_eq(h[0].1.length(), 0)
  assert_eq(h[1].0, 0)
  assert_eq(h[1].1, [5])
  assert_eq(h[2].0, 0)
  assert_eq(h[2].1.length(), 0)
  assert_eq(h[3].0, 1)
  assert_eq(h[3].1.length(), 0)
  // p = 5 時撓消失（同調塌成所有維度都非零）
  let l5 = @cellcx.cx_lens(5, 1, 5)
  assert_eq(@cellcx.cx_betti_all(l5), [1, 1, 1, 1])
  // p = 7 時 ∂_2 可逆 ⟹ 只剩 H_0, H_3
  let l7 = @cellcx.cx_lens(5, 1, 7)
  assert_eq(@cellcx.cx_betti_all(l7), [1, 0, 0, 1])
}

///|
/// [E-Persist][T-Persist-Betti] 持續同調：三角形的邊界（=S¹）與四面體的邊界（=S²）。
///   三角形：3 個頂點在 0，三條邊在 1,2,3 ⟹ H_0 有 2 條有限條碼 + 1 條本質；H_1 有 1 條本質（生於 3）。
test "persistent homology of a circle and a sphere" {
  let circ = @cellcx.cx_from_faces([[0, 1], [1, 2], [0, 2]], 7)
  assert_eq(@cellcx.cx_is_sphere(circ, 1), true)
  let f = @cellcx.filt_with(circ, fn(_k, i) { if _k == 0 { 0 } else { i + 1 } })
  let bars = @cellcx.cx_barcode(f)
  let mut ess0 = 0
  let mut ess1 = 0
  let mut fin0 = 0
  for (d, _b, dd) in bars {
    if d == 0 && dd < 0 {
      ess0 = ess0 + 1
    }
    if d == 0 && dd >= 0 {
      fin0 = fin0 + 1
    }
    if d == 1 && dd < 0 {
      ess1 = ess1 + 1
    }
  }
  assert_eq(ess0, 1)
  assert_eq(fin0, 2)
  assert_eq(ess1, 1)
  // 持續 Betti 數：t = 0 時只有 3 個點；t = 3 時 β0 = β1 = 1
  assert_eq(@cellcx.cx_persistent_betti(f, 0), [3, 0])
  assert_eq(@cellcx.cx_persistent_betti(f, 3), [1, 1])
  // 四面體邊界 = S²：4 個頂點、6 條邊、4 個面
  let sph = @cellcx.cx_from_faces(
    [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]],
    7,
  )
  assert_eq(@cellcx.cx_check_dd(sph), true)
  assert_eq(@cellcx.cx_is_sphere(sph, 2), true)
  assert_eq(@cellcx.cx_euler(sph), 2)
  let g = @cellcx.filt_with(sph, fn(k, _i) { k })
  let summary = @cellcx.cx_barcode_summary(g)
  assert_eq(summary[0], (0, 3, 1))
  assert_eq(summary[1], (1, 3, 0))
  assert_eq(summary[2], (2, 0, 1))
}
