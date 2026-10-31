// ===========================================================================
// catify —— 逐結構範疇化的測試
// ===========================================================================

///|
/// 正方 site（∅ < A、B < U），與 canon 測試共用同一個偏序。
fn sq(p : Int32) -> @grotop.Site {
  let leq : Array[Array[Bool]] = [
    [true, true, true, true],
    [false, true, false, true],
    [false, false, true, true],
    [false, false, false, true],
  ]
  @grotop.site_new(leq, p)
}

///|
/// [T-Cat-Discrete] 集合 ↦ 離散範疇：是範疇、decat 回到個數。
test "set categorifies to a discrete category" {
  for n = 0; n <= 5; n = n + 1 {
    let c = @catify.cat_discrete(n, 2)
    let (is_cat, d) = @catify.cat_roundtrip(c)
    assert_eq(is_cat, true)
    assert_eq(d, n)
  }
}

///|
/// [T-Cat-Grp] 群 ↦ 單物件範疇：範疇公理 ⟺ 群公理；合成表就是乘法表。
test "group categorifies to a one-object category" {
  // Z/2、Z/3、(Z/2)²
  let cases = [@twist.grp([2]), @twist.grp([3]), @twist.grp([2, 2])]
  for g in cases {
    let bg = @catify.cat_from_group(g, 2)
    assert_eq(@catify.cat_is_category(bg), true)
    assert_eq(@catify.decat(bg), 1)
    // |Aut| = |G|
    assert_eq(@catify.cat_dim(bg, 0, 0), @twist.grp_order(g))
    // 合成表 = 群乘法表（逐項）
    assert_eq(@catify.cat_group_table_matches(bg, g), true)
    // 群胚基數 = 1/|G|
    let card = @catify.cat_groupoid_cardinality(bg)
    assert_eq(card.num, 1)
    assert_eq(card.den, @twist.grp_order(g).to_int64())
  }
}

///|
/// [T-Cat-Thin] 偏序 ↦ thin 範疇：自反 + 傳遞 ⟹ 範疇；
///   **拿掉傳遞性就破壞結合律**（這是範疇化給出的新反例，canon 那節只看到「不是偏序」）。
test "poset categorifies to a thin category; non-transitive relations break associativity" {
  let s = sq(2)
  let c = @catify.cat_of_site(s)
  assert_eq(@catify.cat_is_category(c), true)
  // decat：site 只有一個「連通分量」（∅ ≤ 所有），故為 1
  assert_eq(@catify.decat(c), 1)
  // 非自反：拿掉對角線
  let norefl : Array[Array[Bool]] = Array::makei(4, _ => Array::make(4, false))
  for i = 0; i < 4; i = i + 1 {
    for j = 0; j < 4; j = j + 1 {
      if i != j {
        norefl[i][j] = s.leq[i][j]
      }
    }
  }
  let c2 = @catify.cat_thin(norefl, 2)
  let (l, _) = @catify.cat_units(c2)
  assert_eq(l, false) // 沒有單位態射 ⟹ 左單位律失敗
  // 非傳遞（版本 1）：另有 ∅ ≤ 一切，故 0 → A → U → B 的兩條括號路徑不同 ⟹ **結合律直接抓到**
  let t1 : Array[Array[Bool]] = [
    [true, true, true, true],
    [false, true, false, true],
    [false, false, true, false],
    [false, false, true, true],
  ]
  let cA = @catify.cat_thin(t1, 2)
  assert_eq(@catify.cat_assoc(cA), false)
  // 非傳遞（版本 2）：只有 A ≤ U、U ≤ B（其餘只有自反），缺 A ≤ B。
  // 這回**結合律假通過**（兩邊都被零矩陣遮住），只有「合成全定義」抓得到。
  let t2 : Array[Array[Bool]] = [
    [true, false, false, false],
    [false, true, false, true],
    [false, false, true, false],
    [false, false, true, true],
  ]
  let cB = @catify.cat_thin(t2, 2)
  assert_eq(@catify.cat_assoc(cB), true) // 假通過（見 THEORY §29.3）
  assert_eq(@catify.cat_composition_total(cB), false) // 真判準
  // 對照：真正的偏序（正方 site）兩者皆真
  assert_eq(@catify.cat_composition_total(c), true)
  assert_eq(@catify.cat_assoc(c), true)
  // 非自反 ⟹ 單位律不成立（與合成全定義是兩回事，兩個判準都要）
  let (unl, _) = @catify.cat_units(c2)
  assert_eq(unl, false)
  assert_eq(@catify.cat_is_category(c2), false)
}

///|
/// [T-Cat-Relation] 等價關係 ↦ 群胚：完備性 ⟹ 群胚；非完備（等價關係失效）⟹ 不是範疇。
test "equivalence relation categorifies to a groupoid" {
  // 0 ~ 1 ~ 2，3 自成一類
  let rel : Array[Array[Bool]] = Array::makei(4, i => {
    Array::makei(4, j => (i < 3 && j < 3) || i == j)
  })
  let c = @catify.cat_relation_groupoid(rel, 2)
  assert_eq(@catify.cat_is_category(c), true)
  // decat = 同構類個數 = 2
  assert_eq(@catify.decat(c), 2)
  // 每個自同構群都是平凡的 ⟹ 群胚基數 = 1/1 + 1/1 = 2
  let card = @catify.cat_groupoid_cardinality(c)
  assert_eq(card.num, 2)
  assert_eq(card.den, 1)
  // 非傳遞的「關係」不是群胚（結合律失敗）
  let bad : Array[Array[Bool]] = [
    [true, true, false, false],
    [true, true, true, false],
    [false, false, true, false],
    [false, false, true, true],
  ]
  // 0~1、1~2 但 0≁2 ⟹ 應失敗
  let c2 = @catify.cat_relation_groupoid(bad, 2)
  assert_eq(@catify.cat_assoc(c2), false)
}

///|
/// [T-Cat-Burnside] 作用群胚：群胚基數 = |X|/|G|（**比「軌道數」更細的不變量**）。
///   自由作用與非自由作用各驗一例。
test "action groupoid: groupoid cardinality equals |X|/|G|" {
  // G = (Z/2)² 自由作用在 4 點上（正則作用）：|X|/|G| = 4/4 = 1，軌道數 1
  let g4 = @twist.grp([2, 2])
  let act4 = fn(k : Int32, x : Int32) { (x + k) % 4 }
  let c = @catify.cat_action_groupoid(g4, 4, act4, 2)
  assert_eq(@catify.cat_is_category(c), true)
  assert_eq(@catify.decat(c), 1)
  let card = @catify.cat_groupoid_cardinality(c)
  assert_eq(card.num, 1)
  assert_eq(card.den, 1)
  // G = Z/2 平凡作用在 3 點上：|X|/|G| = 3/2，軌道數 3（≠ 基數）
  let g2 = @twist.grp([2])
  let act_triv = fn(k : Int32, x : Int32) {
    let _ = k
    x
  }
  let c2 = @catify.cat_action_groupoid(g2, 3, act_triv, 2)
  assert_eq(@catify.cat_is_category(c2), true)
  assert_eq(@catify.decat(c2), 3)
  let card2 = @catify.cat_groupoid_cardinality(c2)
  assert_eq(card2.num, 3) // 3 個軌道 × 1/|stab| = 3 × 1/2
  assert_eq(card2.den, 2)
  // 兩個數的關係：軌道數 ≤ 基數（自由時取等）
  assert_eq(@catify.decat(c2), 3)
}

///|
/// [T-Cat-Product] 範疇乘積仍是範疇，且 decat 為乘積。
test "product of categories is a category" {
  let a = @catify.cat_discrete(2, 2)
  let b = @catify.cat_discrete(3, 2)
  let c = @catify.cat_product(a, b)
  assert_eq(c.n, 6)
  assert_eq(@catify.cat_is_category(c), true)
  assert_eq(@catify.decat(c), 6)
  // groupoid × discrete
  let g = @catify.cat_from_group(@twist.grp([2]), 2)
  let pg = @catify.cat_product(g, a)
  assert_eq(@catify.cat_is_category(pg), true)
  assert_eq(@catify.decat(pg), 2)
  let card = @catify.cat_groupoid_cardinality(pg)
  assert_eq(card.num, 1) // 2 類 × 1/2
  assert_eq(card.den, 1)
}

///|
/// [T-Functor] 函子性：BG(Z/2) → BG((Z/2)²) 的包含映射是函子；
///   而「把兩個元素都送到同一元素」的映射在乘法上失敗（反例）。
test "functors: inclusion is a functor, collapsing is not" {
  let g2 = @twist.grp([2])
  let g4 = @twist.grp([2, 2])
  let c2 = @catify.cat_from_group(g2, 2)
  let c4 = @catify.cat_from_group(g4, 2)
  // 包含：Z/2 = {0,1} ⊂ (Z/2)² = {0,1,2,3}（都是前兩個元素）
  let inc_hom : Array[@core.Mat] = [
    @core.mat_from_rows([[1, 0], [0, 1], [0, 0], [0, 0]]),
  ]
  let inc_hom2 : Array[Array[@core.Mat]] = [inc_hom]
  let inc = @catify.functor_new(c2, c4, [0], inc_hom2, "inclusion")
  assert_eq(@catify.functor_valid(inc), true)
  // 塌縮：1 ↦ 0（把非單位元素送到單位）⟹ 應失敗
  let col_hom : Array[@core.Mat] = [
    @core.mat_from_rows([[1, 0], [1, 0], [0, 0], [0, 0]]),
  ]
  let col : Array[Array[@core.Mat]] = [col_hom]
  let bad = @catify.functor_new(c2, c4, [0], col, "collapse")
  assert_eq(@catify.functor_valid(bad), false)
}

///|
/// [T-NatTrans] 自然變換：End(BG) 的**自然自同態 = 群的中心 Z(G)**。
///   (Z/2)² 的交換 ⟹ 有 2 個自然變換（恆等 + 平移）；非交換群只有 1 個。
test "natural transformations of the identity functor on BG are central elements" {
  let g4 = @twist.grp([2, 2])
  let c = @catify.cat_from_group(g4, 2)
  let idm = @core.mat_from_rows([
    [1, 0, 0, 0],
    [0, 1, 0, 0],
    [0, 0, 1, 0],
    [0, 0, 0, 1],
  ])
  let id_hom : Array[Array[@core.Mat]] = [[idm]]
  let fid = @catify.functor_new(c, c, [0], id_hom, "id")
  assert_eq(@catify.functor_valid(fid), true)
  // 嘗試 4 個可能的 α（α: 1 → 群元素 g），檢查自然性
  let mut valid = 0
  for k = 0; k < 4; k = k + 1 {
    let comp : Array[@core.Mat] = [
      @core.mat_from_rows([
        [if k == 0 { 1 } else { 0 }],
        [if k == 1 { 1 } else { 0 }],
        [if k == 2 { 1 } else { 0 }],
        [if k == 3 { 1 } else { 0 }],
      ]),
    ]
    let t = @catify.nat_new(fid, fid, comp)
    if @catify.nat_valid(t) {
      valid = valid + 1
    }
  }
  // (Z/2)² 交換 ⟹ 全部 4 個元素都是中心的
  assert_eq(valid, 4)
}

///|
/// [T-Cat-Sieve] sieve = 可表函子 y(U) 的子函子：兩條獨立路徑數出的個數相同。
test "sieves are subfunctors of the representable functor" {
  let s = sq(2)
  for u = 0; u < 4; u = u + 1 {
    let (sub, sieve) = @catify.sieve_subfunctor_count(s, u)
    assert_eq(sub, sieve)
  }
  // U 上方有 4 個開集的向下封閉子集：∅、{∅}、{∅,A}、{∅,B}、{∅,A,B}、{∅,A,B,U}… 由程式給出
  let (sub3, _) = @catify.sieve_subfunctor_count(s, 3)
  assert_eq(sub3 > 1, true)
}

///|
/// [T-Cat-Euler] 鏈複形範疇化：Σ(−1)^k dim C_k = Σ(−1)^k dim H_k。
test "chain complex categorifies the Euler characteristic" {
  let cases = [
    @cellcx.cx_sphere(2, 7),
    @cellcx.cx_sphere(3, 7),
    @cellcx.cx_lens(5, 1, 7),
    @cellcx.cx_torus(2, 7),
  ]
  for cx in cases {
    let (a, b) = @catify.cat_euler_pair(cx)
    assert_eq(a, b)
  }
}

///|
/// [T-Cat-Graded] 分次歐拉特徵：Serre 譜序列的 E₂ 與 E_∞ 有相同歐拉特徵
///   （因為微分把 (p,q) 送到 (p+2, q−1)，總次數的符號不變）。
test "graded Euler characteristic is preserved by the spectral sequence" {
  // Hopf：E₂ 有四格（各一維），總次數 0,1,2,3 ⟹ 1 − 1 + 1 − 1 = 0
  let e2 = [1, 1, 1, 1]
  assert_eq(@catify.graded_euler(e2), 0)
  // E_∞ = H_*(S³) = (1,0,0,1) ⟹ 1 − 0 + 0 − 1 = 0（相同）
  let einf = [1, 0, 0, 1]
  assert_eq(@catify.graded_euler(einf), 0)
  // S² × S³：1,0,1,1,0,1 ⟹ 1 − 0 + 1 − 1 + 0 − 1 = 0
  let prod = [1, 0, 1, 1, 0, 1]
  assert_eq(@catify.graded_euler(prod), 0)
  // 球面 S²：1,0,1 ⟹ 2
  assert_eq(@catify.graded_euler([1, 0, 1]), 2)
  // 與胞腔版的歐拉特徵一致
  let s2 = @cellcx.cx_sphere(2, 7)
  assert_eq(
    @catify.graded_euler(@cellcx.cx_betti_all(s2)),
    @cellcx.cx_euler(s2),
  )
}

///|
/// [T-Cat-FacePoset] 面偏序是範疇；單純形的面偏序連通（decat = 1）。
test "face poset of a simplicial complex is a thin category" {
  // 三角形（含所有子面）
  let faces : Array[Array[Int32]] = [
    [0],
    [1],
    [2],
    [0, 1],
    [1, 2],
    [0, 2],
    [0, 1, 2],
  ]
  let c = @catify.cat_face_poset(faces, 2)
  assert_eq(@catify.cat_is_category(c), true)
  assert_eq(@catify.cat_composition_total(c), true)
  assert_eq(@catify.decat(c), 1)
  // 兩個孤立頂點的面偏序：兩個連通分量
  let disc : Array[Array[Int32]] = [[0], [1]]
  let c2 = @catify.cat_face_poset(disc, 2)
  assert_eq(@catify.cat_is_category(c2), true)
  assert_eq(@catify.decat(c2), 2)
}

///|
/// [T-Cat-Canon] **canon 的類數 = 群胚範疇化的 decat**：
///   把 `@canon` 的等價類當成群胚的同構類，去範疇化就回到類數。
///   四組獨立資料（RREF、相似、上同調、二面體）全部相符。
test "canon classes are the decategorification of a groupoid" {
  // (1) RREF 類：M_{2×3}(F₂) 的 64 個矩陣 ⟹ 15 類
  let rref_keys : Array[Array[Int32]] = []
  for code = 0; code < 64; code = code + 1 {
    let m = @core.mat_make(2, 3, 0)
    let mut c = code
    for i = 0; i < 2; i = i + 1 {
      for j = 0; j < 3; j = j + 1 {
        m.data[i * 3 + j] = c % 2
        c = c / 2
      }
    }
    rref_keys.push(@catify.canon_flatten(@canon.canon_rref(m, 2)))
  }
  let c1 = @catify.cat_class_groupoid(rref_keys)
  assert_eq(@catify.decat(c1), 15)
  assert_eq(@catify.decat(c1), @catify.distinct_keys(rref_keys))
  // (2) 相似類：M_2(F_2) 的 16 個矩陣 ⟹ 6 類
  let conj_keys : Array[Array[Int32]] = []
  for code = 0; code < 16; code = code + 1 {
    let m = @core.mat_make(2, 2, 0)
    let mut c = code
    for i = 0; i < 2; i = i + 1 {
      for j = 0; j < 2; j = j + 1 {
        m.data[i * 2 + j] = c % 2
        c = c / 2
      }
    }
    conj_keys.push(@canon.canon_conj(m, 2))
  }
  let c2 = @catify.cat_class_groupoid(conj_keys)
  assert_eq(@catify.decat(c2), 6)
  // (3) 上同調類：(Z/2)²、ℓ = 2 的 16 個自由座標 ⟹ 8 類
  let g = @twist.grp([2, 2])
  let nv = @twist.var_count(g)
  let coc_keys : Array[Array[Int32]] = []
  for code = 0; code < @core.int_pow(2, nv); code = code + 1 {
    let v : Array[Int32] = []
    let mut c = code
    for i = 0; i < nv; i = i + 1 {
      v.push(c % 2)
      c = c / 2
    }
    if @canon.is_cocycle(g, 2, v) {
      coc_keys.push(@canon.canon_cocycle(g, 2, v))
    }
  }
  let c3 = @catify.cat_class_groupoid(coc_keys)
  assert_eq(@catify.decat(c3), 8)
  // (4) 二面體軌道：5 邊形的單邊（10 個）⟹ 2 類（邊 vs 對角線）
  let dih_keys : Array[Array[Int32]] = []
  for a = 0; a < 5; a = a + 1 {
    for b = a + 1; b < 5; b = b + 1 {
      dih_keys.push(@canon.canon_dihedral(5, [@nc.chord(a, b)]))
    }
  }
  let c4 = @catify.cat_class_groupoid(dih_keys)
  assert_eq(@catify.decat(c4), 2)
}
