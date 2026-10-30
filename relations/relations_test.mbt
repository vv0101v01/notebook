///|
/// [T-Rel-Scale] 相對剖面抹掉整體尺度：ys = c·xs ⟹ profile(xs) = profile(ys)。
test "relative profile is scale invariant" {
  assert_eq(
    @relations.check_relative_scale_invariance([3, 6, 9, 12], 5, 10007),
    true,
  )
  assert_eq(
    @relations.check_relative_scale_invariance([1, 2, 4, 8], 3, 11),
    true,
  )
  assert_eq(@relations.relative(6, 3, 10007), 2)
  assert_eq(@relations.relative(5, 5, 10007), 1)
  assert_eq(@relations.relative_profile([2, 4, 8], 11), [1, 2, 4])
}

///|
/// [T-Dual-Rank][T-Dual-Radon] 列秩 = 行秩（含零化度）；Radon 的 R 與 Rᵀ 同秩且單射。
test "rank/nullity duality and Radon injectivity duality" {
  let rng = @core.rng_seed(11)
  for p in [7, 10007] {
    for n = 2; n <= 4; n = n + 1 {
      let m = @core.mat_build(n, n + 1, (_, _) => @core.rng_below(rng, p))
      assert_eq(@relations.dual_rank_nullity(m, p), true)
    }
  }
  for n in [2, 3, 5] {
    let (same_rank, injective, rk, n2) = @relations.dual_radon_injectivity(
      n, 10007,
    )
    assert_eq(same_rank, true)
    assert_eq(injective, true)
    assert_eq(rk, n2)
  }
}

///|
/// [T-Dual-Chain] 下鏈／上鏈對偶：∂∂ = 0，且同調維數 = 上同調維數（兩條獨立路徑）。
///   並與 metric 的同調計算對照：VR(C₄,1) 的 β = (1,1,0)。
test "chain/cochain duality gives equal homology and cohomology dimensions" {
  let (dd4, eq4) = @relations.dual_chain_cochain(
    @metric.mspace_cycle(4, 1),
    1,
    2,
  )
  let (dd5, eq5) = @relations.dual_chain_cochain(
    @metric.mspace_cycle(5, 1),
    1,
    2,
  )
  let (dd6, eq6) = @relations.dual_chain_cochain(
    @metric.mspace_cycle(6, 1),
    2,
    2,
  )
  assert_eq(dd4, true)
  assert_eq(eq4, true)
  assert_eq(dd5, true)
  assert_eq(eq5, true)
  assert_eq(dd6, true)
  assert_eq(eq6, true)
  let betti = @metric.vr_betti_all(@metric.mspace_cycle(4, 1), 1)
  assert_eq(betti[0], 1)
  assert_eq(betti[1], 1)
}

///|
/// [T-Dual-Tensor] 超行列式在 6 個指標置換下不變 ——「張量的對偶」不改變判別量。
test "hyperdeterminant is invariant under the 6 index permutations" {
  let rng = @core.rng_seed(2026)
  let mut ok = true
  for _t = 0; _t < 25; _t = _t + 1 {
    let t = @tensor.t3_of(2, 2, 2, 3, (_, _, _) => @core.rng_below(rng, 3))
    if !@relations.dual_tensor_permutation(t) {
      ok = false
    }
  }
  assert_eq(ok, true)
}

///|
/// [T-Contrast-Partition] 對比分割：onlyA + onlyB + both 恰為 A ∪ B，三塊互斥。
///   取蘊含表的兩列（rank ≤ 1 與 Det = 0）作示範：因 rank ≤ 1 ⟹ Det = 0，故 onlyA 必為 0。
test "contrast partitions the union of two predicate sets" {
  let table = @relations.tensor_predicate_table()
  let (na, nb, nc) = @relations.contrast_counts(table[0], table[1])
  assert_eq(na, 0) // rank ≤ 1 的張量必然 Det = 0
  assert_eq(@relations.check_contrast_partition(table[0], table[1]), true)
  let (oa, ob, bo) = @relations.contrast(table[0], table[1])
  assert_eq(oa.length(), 6561)
  assert_eq(na + nb + nc, nc + nb) // onlyA = 0 ⟹ 三塊之和 = A ∪ B = Det=0 的個數
  // 一般情形：兩族的併集大小確實等於三塊之和
  let (na2, nb2, nc2) = @relations.contrast_counts(table[1], table[3])
  let mut union = 0
  for i = 0; i < table[1].length(); i = i + 1 {
    if table[1][i] || table[3][i] {
      union = union + 1
    }
  }
  assert_eq(na2 + nb2 + nc2, union)
  assert_eq(@relations.check_contrast_partition(table[1], table[3]), true)
  // 三塊互斥：交集恆為空
  let mut disjoint = true
  for i = 0; i < oa.length(); i = i + 1 {
    if bo[i] && (oa[i] || ob[i]) {
      disjoint = false
    }
  }
  assert_eq(disjoint, true)
}

///|
/// [T-Impl-Closure] 由 6561 個 F₃ 張量算出的蘊含矩陣（固定值），
///   以及傳遞閉包與等價類的計算。列 = 來源謂詞，行 = 目標謂詞：
///   0: rank ≤ 1   1: Det = 0   2: rank-2 分解數 = 0   3: rank = 3   4: Det ≠ 0
test "implication structure over all 6561 tensors" {
  let table = @relations.tensor_predicate_table()
  let m = @relations.implication_matrix(table)
  let expect = [
    [true, true, true, false, false],
    [false, true, false, false, false],
    [false, false, true, false, false],
    [false, false, true, true, false],
    [false, false, false, false, true],
  ]
  assert_eq(m, expect)
  // 由資料導出的三條具體蘊含
  assert_eq(@relations.implies(table[0], table[1]), true) // rank ≤ 1 ⟹ Det = 0
  assert_eq(@relations.implies(table[0], table[2]), true) // rank ≤ 1 ⟹ rank-2 分解數 = 0
  assert_eq(@relations.implies(table[3], table[2]), true) // rank = 3 ⟹ rank-2 分解數 = 0
  assert_eq(@relations.implies(table[4], table[3]), false) // Det ≠ 0 ⇏ rank = 3
  // 傳遞閉包：沒有新的蘊含（矩陣本身已傳遞），也沒有等價（反向皆不成立）
  let closure = @relations.implication_closure(m, 5)
  assert_eq(closure, expect)
  assert_eq(@relations.equivalences(closure).length(), 0)
}

///|
/// [T-Ratio-Radon][T-Ratio-Flip] 兩個「比率不變量」：
///   Radon 的 (Σ Rf) : (Σ f) = (n+1) : 1（對任意 f）；翻轉圖的 E : V = (n−3) : 2。
test "ratio invariants: Radon total mass and flip graph edge/vertex" {
  for n in [2, 3, 5] {
    for seed = 1; seed <= 3; seed = seed + 1 {
      let f = Array::makei(n * n, i => (i * seed * 7 + 1) % 10007)
      match @relations.radon_total_relative(n, 10007, f) {
        Some(v) => assert_eq(v, n + 1)
        None => fail("Σf ≠ 0 時比值必須存在")
      }
    }
    // Σf ≡ 0 時比值不存在（零均值是定理的必要前提）
    let zero_mean = Array::makei(n * n, i => {
      if i == 0 {
        1
      } else if i == 1 {
        10006
      } else {
        0
      }
    })
    match @relations.radon_total_relative(n, 10007, zero_mean) {
      Some(_) => fail("零均值時不應給出比值")
      None => ()
    }
  }
  assert_eq(@relations.flip_edge_vertex_ratio(5), (1, 1))
  assert_eq(@relations.flip_edge_vertex_ratio(6), (3, 2))
  assert_eq(@relations.flip_edge_vertex_ratio(7), (2, 1))
  // 非恆定時必須回 None（而不是硬給一個值）
  match @relations.constant_ratio([(1, 2), (1, 3)]) {
    Some(_) => fail("比值不恆定時應回 None")
    None => ()
  }
}

///|
/// [E-Collect][E-CollectInto] 五類關係的收集結果全部成立，並可寫入持久賬本且通過稽核。
test "collect relations into the persistent ledger" {
  let recs = @relations.collect(2, 10007)
  assert_eq(recs.length(), 4)
  let mut all = true
  for r in recs {
    if !r.holds {
      all = false
    }
  }
  assert_eq(all, true)
  let base = @ledger.observe(@ledger.empty(), [1, 1, 1])
  let (l2, cnt) = @relations.collect_into_ledger(base, 2, 10007)
  assert_eq(cnt, 4)
  assert_eq(@ledger.ledger_len(l2), 5)
  assert_eq(@ledger.verify(l2), true)
  assert_eq(@ledger.fork_index(base, l2), 1)
  // 寫入的記錄可讀回
  match @ledger.entry_at(l2, 4) {
    Some(e) => {
      assert_eq(e.kind, 2)
      assert_eq(e.values.length(), 4)
    }
    None => fail("第 4 條記錄應存在")
  }
}
