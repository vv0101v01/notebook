///|
/// 測試 site：0 = ∅、1 = A、2 = B、3 = U（A、B 不相交，皆 ⊆ U）。
fn sq_site(p : Int32) -> @grotop.Site {
  let leq : Array[Array[Bool]] = [
    [true, true, true, true],
    [false, true, false, true],
    [false, false, true, true],
    [false, false, false, true],
  ]
  @grotop.site_new(leq, p)
}

///|
/// [T-Site] 偏序公理與交運算。
test "site axioms and meets" {
  let s = sq_site(2)
  assert_eq(@grotop.site_valid(s), true)
  assert_eq(@grotop.site_meet(s, 1, 3), 1)
  assert_eq(@grotop.site_meet(s, 1, 2), 0)
  assert_eq(@grotop.site_meet(s, 3, 3), 3)
}

///|
/// [T-Sieve] sieve 的向下封閉化與拉回。
test "sieve closure and pullback" {
  let s = sq_site(3)
  let sv = @grotop.sieve_generate(s, [1, 2])
  // 生成 {A, B} 的 sieve 必須加入 ∅
  assert_eq(@grotop.sieve_elems(s, sv), [0, 1, 2])
  assert_eq(@grotop.sieve_is_down_closed(s, sv), true)
  // 沿 A ⊆ U 的拉回
  let pu = @grotop.sieve_pull(s, @grotop.sieve_max(s, 3), 1)
  assert_eq(@grotop.sieve_elems(s, pu), [0, 1])
  // 最大 sieve
  assert_eq(@grotop.sieve_elems(s, @grotop.sieve_max(s, 3)), [0, 1, 2, 3])
}

///|
/// [T-Top] 三條公理：離散拓撲、混沌拓撲、由覆蓋族生成者皆合法。
test "Grothendieck topologies satisfy the axioms" {
  let s = sq_site(2)
  assert_eq(@grotop.top_valid(@grotop.top_discrete(s)), true)
  assert_eq(@grotop.top_valid(@grotop.top_chaotic(s)), true)
  let t = @grotop.top_of_families(s, [(3, [1, 2])])
  assert_eq(@grotop.top_valid(t), true)
  // 覆蓋 {A,B} 的 sieve 已被收錄
  assert_eq(@grotop.covers(t, 3, @grotop.sieve_generate(s, [1, 2])), true)
}

///|
/// [T-Top] 反例：(T1) 失敗與 (T2) 失敗都被偵測到。
test "broken topologies are rejected" {
  let s = sq_site(2)
  // 拿掉最大 sieve ⟹ (T1) 失敗
  let bad = @grotop.top_of_families(s, [])
  bad.cov[3] = []
  assert_eq(@grotop.top_axiom_max(bad), false)
  assert_eq(@grotop.top_valid(bad), false)
  // 只宣告 {A} 覆蓋 U（sieve {∅,A}），沿 B ⊆ U 的拉回是 {∅}，
  // 但 B 上的最大 sieve 是 {∅,B} ⟹ (T2) 失敗
  let bad2 = @grotop.top_of_families(s, [])
  bad2.cov[3] = [@grotop.sieve_generate(s, [1])]
  assert_eq(@grotop.top_axiom_max(bad2), false)
  assert_eq(@grotop.top_axiom_pull(bad2), false)
}

///|
/// [T-Sheaf] 常數預層不是層；「點上的函數」層是層。
test "sheaf condition" {
  let s = sq_site(2)
  let t = @grotop.top_of_families(s, [(3, [1, 2])])
  let fam = [1, 2]
  // 常數預層：dims 全 1、限制為單位
  let dims = [1, 1, 1, 1]
  let cf = @grotop.pf_new(s, dims, fn(a, b) {
    let _ = b
    Some(@core.mat_make(1, 1, if a == 0 { 0 } else { 1 }))
  })
  let (inj1, ex1, _, _, _) = @grotop.sheaf_check(cf, 3, fam)
  assert_eq(inj1, true)
  assert_eq(ex1, false) // 1 ≠ 2：常數預層不是層
  assert_eq(@grotop.is_sheaf(cf, t), false)
  // 「點上的函數」層：F(∅)=0, F(A)=F(B)=1, F(U)=2，限制為投影
  let dims2 = [0, 1, 1, 2]
  let f = @grotop.pf_new(s, dims2, fn(a, b) {
    let da = match a {
      0 => 0
      1 => 1
      2 => 1
      _ => 2
    }
    let db = match b {
      0 => 0
      1 => 1
      2 => 1
      _ => 2
    }
    let m = @core.mat_make(da, db, 0)
    if a == b {
      for i = 0; i < da; i = i + 1 {
        m.data[i * db + i] = 1
      }
    } else if b == 3 && (a == 1 || a == 2) {
      // 投影：A → U 取第一個座標、B → U 取第二個
      m.data[0 * db + 0] = if a == 1 { 1 } else { 0 }
      m.data[0 * db + 1] = if a == 1 { 0 } else { 1 }
    }
    Some(m)
  })
  let (inj2, ex2, k0, k1, r0) = @grotop.sheaf_check(f, 3, fam)
  assert_eq(inj2, true)
  assert_eq(ex2, true)
  assert_eq(k0, 0)
  assert_eq(k1, 2)
  assert_eq(r0, 2)
  assert_eq(@grotop.is_sheaf(f, t), true)
}

///|
/// [E-Plus] 加號構造：常數預層 F⁺(U) 的維數 = 相容族維數 = 2，
///   且（在此 site 上）一次加號就得到層。
test "plus construction of the constant presheaf" {
  let s = sq_site(2)
  let t = @grotop.top_of_families(s, [(3, [1, 2])])
  let fam = [1, 2]
  let cf = @grotop.pf_new(s, [1, 1, 1, 1], fn(a, b) {
    let _ = b
    Some(@core.mat_make(1, 1, if a == 0 { 0 } else { 1 }))
  })
  assert_eq(@grotop.pf_plus_dim(cf, 3, fam), 2)
  assert_eq(@grotop.pf_plus_dim_all(cf, t, 3), 2)
}
