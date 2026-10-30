///|
/// evolve 的測試：Ledger 關係推導器本身、以及五類演變下恆定關係的「先導出、後轉移」驗證。
test "[D-Derive] 關係推導器：找到真關係、拒絕偽關係" {
  // 觀測 (a,b,c) = (t, 2t+1, t²) 對 t=0..5：關係 b - 2a - 1 = 0 恆定
  let rows : Array[Array[Int32]] = []
  for t = 0; t <= 5; t = t + 1 {
    let _ = rows.push([t, 2 * t + 1, t * t])
  }
  let l = @evolve.rowset_with_const(rows)
  let rels = @evolve.derive_relations(l, 10007, true)
  assert_eq(@evolve.relation_derived(rels, [-1, -2, 1, 0], 10007), true)
  // 常數欄 + c 不滿足任何非平凡常數關係（t² 變動），故 (0,0,0,1) 不成立
  assert_eq(@evolve.holds_exact(l, [0, 0, 0, 1]), false)
  // 交錯驗證：係數 (0,1,0,-1) 不成立
  assert_eq(@evolve.holds_exact(l, [0, 1, 0, -1]), false)
  assert_eq(@evolve.rowset_len(l), 6)
}

///|
test "[E-Flip][Inv-Flip] 翻轉漫遊：對偶為樹 E=V-1、三角數不變、無交叉" {
  let l = @evolve.evolve_flips(5, 12, 11)
  assert_eq(@evolve.rowset_len(l), 13)
  // 欄位 (1, #三角, V_dual, E_dual, 最大度, 交叉對數)
  assert_eq(@evolve.holds_exact(l, [1, 0, -1, 1, 0, 0]), true)
  assert_eq(@evolve.holds_exact(l, [0, 1, -1, 0, 0, 0]), true)
  assert_eq(@evolve.holds_exact(l, [0, 0, 0, 0, 0, 1]), true)
  let rels = @evolve.derive_relations(l, 10007, true)
  assert_eq(@evolve.relation_derived(rels, [1, 0, -1, 1, 0, 0], 10007), true)
  let l2 = @evolve.evolve_flips(6, 12, 99)
  assert_eq(@evolve.holds_exact(l2, [1, 0, -1, 1, 0, 0]), true)
  assert_eq(@evolve.holds_exact(l2, [0, 0, 0, 0, 0, 1]), true)
}

///|
test "[E-Gauge][Inv-Gauge] 規範流：K₀ 秩 = |rad|、d²·|rad| = |G| 沿流守恆" {
  let l = @evolve.evolve_gauge(3, 10, 21)
  assert_eq(@evolve.rowset_len(l), 11)
  // 欄位 (|G|, |rad|, dim Z, d²·|rad|, Σω)
  assert_eq(@evolve.holds_exact(l, [0, -1, 1, 0, 0]), true)
  assert_eq(@evolve.holds_exact(l, [-1, 0, 0, 1, 0]), true)
  let rels = @evolve.derive_relations(l, 10007, true)
  assert_eq(@evolve.relation_derived(rels, [0, -1, 1, 0, 0], 10007), true)
  assert_eq(@evolve.relation_derived(rels, [-1, 0, 0, 1, 0], 10007), true)
  let l4 = @evolve.evolve_gauge(4, 10, 77)
  assert_eq(@evolve.holds_exact(l4, [0, -1, 1, 0, 0]), true)
  assert_eq(@evolve.holds_exact(l4, [-1, 0, 0, 1, 0]), true)
}

///|
test "[E-Radon][Inv-Radon] Radon 平滑迭代下二次型守恆律（mod p 精確）" {
  let l = @evolve.evolve_radon(3, 10007, 8, 31)
  assert_eq(@evolve.rowset_len(l), 9)
  // 欄位 (Σf², Σ(Rf)², (Σf)²)：Σ(Rf)² - 3Σf² - (Σf)² = 0
  assert_eq(@evolve.holds_mod(l, [-3, 1, -1], 10007), true)
  let rels = @evolve.derive_relations(l, 10007, false)
  assert_eq(@evolve.relation_derived(rels, [-3, 1, -1], 10007), true)
  let l2 = @evolve.evolve_radon(3, 10007, 8, 32)
  assert_eq(@evolve.holds_mod(l2, [-3, 1, -1], 10007), true)
}

///|
test "[E-Shear][Inv-Shear] Cayley 超行列式沿 SL₂ 剪切流守恆" {
  let l = @evolve.evolve_shear(3, 10, 41)
  assert_eq(@evolve.rowset_len(l), 11)
  assert_eq(@evolve.holds_exact(l, [-1, 1]), true)
  let rels = @evolve.derive_relations(l, 10007, true)
  assert_eq(@evolve.relation_derived(rels, [-1, 1], 10007), true)
  let l5 = @evolve.evolve_shear(5, 10, 42)
  assert_eq(@evolve.holds_exact(l5, [-1, 1]), true)
}

///|
test "[E-VR][Inv-VR] 尺度增長下 Euler 特徵性與连通性不變" {
  let l = @evolve.evolve_vr(5, 3)
  assert_eq(@evolve.rowset_len(l), 3)
  // 欄位 (1, χ_s, χ_b, β0, β1)
  assert_eq(@evolve.holds_exact(l, [0, 1, -1, 0, 0]), true)
  assert_eq(@evolve.holds_exact(l, [-1, 0, 0, 1, 0]), true)
  let rels = @evolve.derive_relations(l, 10007, true)
  assert_eq(@evolve.relation_derived(rels, [0, 1, -1, 0, 0], 10007), true)
  let l7 = @evolve.evolve_vr(7, 3)
  assert_eq(@evolve.holds_exact(l7, [0, 1, -1, 0, 0]), true)
  assert_eq(@evolve.holds_exact(l7, [-1, 0, 0, 1, 0]), true)
}

///|
test "[T-Evolve-Summary] 五類演變：導出關係並轉移到獨立資料族，全部通過" {
  let r = @evolve.evolve_summary()
  assert_eq(r.length(), 10)
  let mut n_ok = 0
  for x in r {
    if x {
      n_ok = n_ok + 1
    }
  }
  assert_eq(n_ok, 10)
}
