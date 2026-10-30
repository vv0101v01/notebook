///|
/// [T-Hyper-MatRank] F₃ 上 2×2 矩陣的秩超結構 = 帶差區間超化：
///   a ⋆ b = {c : |a−b| ≤ c ≤ min(n, a+b)}，且它滿足全部六條公理（規範超群）。
test "matrix rank hyperstructure is the abs-diff interval and a canonical hypergroup" {
  let (mh, attain) = @hyper.mat_rank_hyper_exhaustive(2, 3)
  let formula = @hyper.abs_diff_hyper(2)
  // 到位性：區間內每個秩都真的出現
  assert_eq(attain, true)
  // 資料驅動的超運算 == 公式化的超運算（逐格相等）
  let mut equal = true
  for a = 0; a <= 2; a = a + 1 {
    for b = 0; b <= 2; b = b + 1 {
      for c = 0; c <= 2; c = c + 1 {
        if @hyper.hyper_contains(mh, a, b, c) !=
          @hyper.hyper_contains(formula, a, b, c) {
          equal = false
        }
      }
    }
  }
  assert_eq(equal, true)
  // 六條公理（0 = 單位元）
  assert_eq(@hyper.hyper_classify(mh, 0), (true, true, true, true, true, true))
  assert_eq(@hyper.is_canonical_hypergroup(mh, 0), true)
  // 單元格大小：rank 1 + rank 1 可達 {0,1,2}（消去與堆疊都發生）
  assert_eq(@hyper.hyper_cell_size(mh, 1, 1), 3)
}

///|
/// [T-Hyper-Interval] 全序集的區間超化：封閉、結合、複製、交換、有逆元，但**無單位元**。
test "interval hyperstructure: associative, reproductive, but no identity" {
  let h = @hyper.interval_hyper(4)
  assert_eq(@hyper.hyper_classify(h, 0), (true, true, true, true, false, true))
  // 結合律的直接見證：(1⋆2)⋆3 與 1⋆(2⋆3) 都等於 {1,2,3}
  let l = @hyper.triple_left(h, 1, 2, 3)
  let r = @hyper.triple_right(h, 1, 2, 3)
  assert_eq(l, r)
  assert_eq(l, [false, true, true, true])
}

///|
/// [T-Hyper-Krasner] Krasner 超域與脆（crisp）群都是規範超群 —— 驗證器的陽性對照。
///   「群 = 所有單元格為單點的超群」，故超化嚴格推廣了群。
test "Krasner hyperfield and crisp group are canonical hypergroups" {
  let k = @hyper.krasner_hyper()
  assert_eq(@hyper.hyper_classify(k, 0), (true, true, true, true, true, true))
  // 1 ⊛ 1 = {0,1}：特徵的不確定性被保留
  assert_eq(@hyper.hyper_cell_size(k, 1, 1), 2)
  let g = @hyper.crisp_cyclic_hyper(5)
  assert_eq(@hyper.is_canonical_hypergroup(g, 0), true)
  let mut crisp = true
  for a = 0; a < 5; a = a + 1 {
    for b = 0; b < 5; b = b + 1 {
      if @hyper.hyper_cell_size(g, a, b) != 1 {
        crisp = false
      }
    }
  }
  assert_eq(crisp, true)
}

///|
/// [T-Hyper-Geodesic] 度量／翻轉圖的測地超化：結合律成立、複製性成立、但**無單位元**
///   ⇒ 不是規範超群。三種載體（C₄、C₅、5 邊形的翻轉圖 C₅）給出同一個指紋。
///   這是一條負面結果：測地區間超結構不是群論型的。
test "geodesic interval hyperstructures are associative but identity-free" {
  let expected = (true, true, true, true, false, true)
  assert_eq(
    @hyper.hyper_classify(@hyper.metric_hyper(@metric.mspace_cycle(4, 1)), 0),
    expected,
  )
  assert_eq(
    @hyper.hyper_classify(@hyper.metric_hyper(@metric.mspace_cycle(5, 1)), 0),
    expected,
  )
  assert_eq(@hyper.hyper_classify(@hyper.flip_hyper(5), 0), expected)
}

///|
/// [E-Potency][T-Potency] 冪零度：a^(*k) 穩定所需的最小 k（以「整塊相乘」倍增）。
///   截斷加法（r=3, a=1）需 3 步；脆循環群 ℤ/n（n = 2..9）恰為 ⌈log₂ n⌉ + 1 步 ——
///   即「集合層的乘法」比逐點加法快一個指數級。
test "hyper-potency is logarithmic for cyclic hypergroups" {
  assert_eq(@hyper.hyper_potency(@hyper.truncated_add_hyper(3), 1, 10), 3)
  let expect = [2, 3, 3, 4, 4, 4, 4, 5]
  for n = 2; n <= 9; n = n + 1 {
    assert_eq(
      @hyper.hyper_potency(@hyper.crisp_cyclic_hyper(n), 1, 20),
      expect[n - 2],
    )
  }
}

///|
/// [T-Hyper-Trunc] 秩截斷超化（張量秩與矩陣秩的公共形式）：
///   單元格大小 = min(r, a+b) + 1，且恆有 0 ∈ a ⋆ b（「零在所有乘積中」）。
test "truncated rank hyperstructure: cell size formula and universal zero" {
  let h = @hyper.tensor_rank_hyper()
  assert_eq(@hyper.hyper_classify(h, 0), (true, true, true, true, false, true))
  let mut cells_ok = true
  let mut zero_ok = true
  for a = 0; a <= 3; a = a + 1 {
    for b = 0; b <= 3; b = b + 1 {
      let cap = if a + b < 3 { a + b } else { 3 }
      if @hyper.hyper_cell_size(h, a, b) != cap + 1 {
        cells_ok = false
      }
      if !@hyper.hyper_contains(h, a, b, 0) {
        zero_ok = false
      }
    }
  }
  assert_eq(cells_ok, true)
  assert_eq(zero_ok, true)
}

///|
/// [T-Hyper-Profile] 超化的「胞尺寸剖面」：interval_hyper(4) 的 |a−b|+1 分佈 = [0,4,6,4,2]，
///   總和 = |A|² = 16；且秩超群與絕對差超群的剖面**逐格相同**（=「秩律即絕對差律」的另一面）。
test "hyper cell size profile" {
  let h = @hyper.interval_hyper(4)
  let prof = @hyper.hyper_cell_profile(h)
  assert_eq(prof, [0, 4, 6, 4, 2])
  let mut sum = 0
  for c in prof {
    sum = sum + c
  }
  assert_eq(sum, 16)
  let (rank_hyper, canonical) = @hyper.mat_rank_hyper_exhaustive(2, 3)
  assert_eq(canonical, true)
  assert_eq(
    @hyper.hyper_cell_profile(rank_hyper),
    @hyper.hyper_cell_profile(@hyper.abs_diff_hyper(2)),
  )
}
