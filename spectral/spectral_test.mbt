///|
/// [T-CH][T-TrDet] Cayley–Hamilton 與係數恆等式：χ_A(A) = 0、c₀ = (−1)ⁿdet A、cₙ₋₁ = −tr A。
test "Cayley-Hamilton and coefficient identities on random matrices" {
  let rng = @core.rng_seed(20261028)
  for p in [7, 11, 13, 17] {
    for n = 2; n <= 4; n = n + 1 {
      for _t = 0; _t < 6; _t = _t + 1 {
        let a = @core.mat_build(n, n, (_, _) => @core.rng_below(rng, p))
        assert_eq(@spectral.check_cayley_hamilton(a, p), true)
        assert_eq(@spectral.check_char_poly_coeffs(a, p), true)
        assert_eq(@spectral.check_trace_square(a, p), true)
      }
    }
  }
}

///|
/// [T-Spec-Radon] RᵀR = nI + J 的譜：χ(x) = (x−n)^{n²−1}(x−(n²+n))。
test "Radon Gram operator spectrum is explicit" {
  for n in [2, 3] {
    let (chi, ok) = @spectral.radon_gram_char_poly(n, 10007)
    assert_eq(ok, true)
    assert_eq(chi.length(), n * n + 1)
  }
}

///|
/// [T-Spec-Chi-Formula] 手徵算子的譜（奇 d：純量；偶 d：x²−s 的幂），且需要 √−1。
test "chirality spectrum formula and the p = 1 mod 4 precondition" {
  for d = 1; d <= 4; d = d + 1 {
    assert_eq(@spectral.check_chirality_formula(d, 13), true)
  }
  // p = 7 ≡ 3 (mod 4)：沒有 √−1 ⇒ 拒絕構造（舊版會靜默產生錯矩陣）
  assert_eq(@gauge.clifford_available(7), false)
  assert_eq(@spectral.check_chirality_formula(2, 7), false)
  assert_eq(@gauge.check_clifford(2, 7), false)
  assert_eq(@gauge.check_clifford(2, 5), true)
}

///|
/// [T-Spec-Lap-Cycle] C_n 的 Laplace 譜 = {2 − ω^k − ω^{−k}}（需 n | p−1）。
test "cycle Laplacian spectrum via roots of unity" {
  assert_eq(@spectral.check_cycle_laplacian_spectrum(3, 7), true)
  assert_eq(@spectral.check_cycle_laplacian_spectrum(4, 13), true)
  assert_eq(@spectral.check_cycle_laplacian_spectrum(5, 11), true)
  // n ∤ p−1 時沒有 n 次本原根 ⇒ 拒絕（不是假裝算出來）
  assert_eq(@spectral.check_cycle_laplacian_spectrum(5, 7), false)
  // 對照：F₅^× 的生成元 2 是 4 次本原根，故 C₄ 在 p=5 上可以譜化
  assert_eq(@radon.root_of_unity(4, 5), 2)
}

///|
/// [T-Spec-Perm] 置換矩陣的 χ = Π(x^{len} − 1)：由矩陣與由循環型兩條路徑互相比對。
test "permutation characteristic polynomial equals cycle-type product" {
  assert_eq(@spectral.check_perm_char_poly([1, 2, 0, 3, 4], 7), true)
  assert_eq(@spectral.check_perm_char_poly([1, 0, 3, 2, 4], 7), true)
  assert_eq(@spectral.check_perm_char_poly([0, 1, 2, 3, 4], 7), true)
  assert_eq(@spectral.check_perm_char_poly([3, 2, 1, 0], 11), true)
}

///|
/// [T-Spec-Isospectral] 譜不決定結構：K_{1,4} 與 C₄⊔K₁ 同（鄰接）譜但直徑 2 vs ∞。
test "isospectral but non-isometric graphs" {
  let (same, d_star, d_cyc) = @spectral.isospectral_star_vs_cycle(7)
  assert_eq(same, true)
  assert_eq(d_star, 2)
  assert_eq(d_cyc, -1)
}

///|
/// [T-Spec-Idempotent] 投影 P = A(AᵀA)⁻¹Aᵀ：P² = P、譜 ⊆ {0,1}、tr P = rank P。
test "projector is idempotent with trace equal to rank" {
  let a = @core.mat_from_rows([[1, 0], [0, 1], [1, 1]])
  match @spectral.projector(a, 7) {
    Some(pp) => {
      let (idem, only01, tr, rk) = @spectral.check_idempotent_theorem(pp, 7)
      assert_eq(idem, true)
      assert_eq(only01, true)
      assert_eq(tr, 2)
      assert_eq(rk, 2)
      assert_eq(tr, rk)
      // 譜確實是 {1, 1, 0}
      let roots = @spectral.spectrum_roots(pp, 7)
      assert_eq(roots, [(0, 1), (1, 2)])
    }
    None => fail("AᵀA 可逆，投影必須存在")
  }
  // 秩不足時拒絕
  let dep = @core.mat_from_rows([[1, 0, 2], [0, 1, 1], [1, 1, 3]])
  match @spectral.projector(dep, 7) {
    Some(_) => fail("秩不足時投影不應存在")
    None => ()
  }
}

///|
/// [T-Spec-RegularRep] 扭曲群代數的左正則表示：tr ρ(e) = |G|，其餘跡為 0。
test "twisted regular representation trace separates the identity" {
  let g = @twist.grp([2, 2])
  let nv = @twist.var_count(g)
  let vec = Array::makei(nv, i => if i == 0 { 1 } else { 0 })
  let o = @twist.mk_omega(g, 2, 5, vec)
  let (tr_id, others) = @spectral.check_regular_rep_trace(o, 5)
  assert_eq(tr_id, 4)
  assert_eq(others, 0)
}

///|
/// [T-Spec-Conj] 譜在共軛下不變（置換與剪切兩類 P 各驗一次）——譜化版的「規範不變量」。
test "spectrum is invariant under conjugation" {
  let rng = @core.rng_seed(7)
  for p in [7, 11] {
    for n = 2; n <= 4; n = n + 1 {
      for _t = 0; _t < 4; _t = _t + 1 {
        let a = @core.mat_build(n, n, (_, _) => @core.rng_below(rng, p))
        assert_eq(@spectral.check_spectral_conjugation(a, p), true)
      }
    }
  }
}

///|
/// [T-Spec-Split] 分裂時 Σλ = tr、Πλ = det；可對角化的判定與特徵空間維數一致。
test "spectral trace/det identities and diagonalizability" {
  let a = @core.mat_from_rows([[1, 2], [2, 4]])
  let (split, diag) = @spectral.check_diagonalizable(a, 7)
  assert_eq(split, true)
  assert_eq(diag, true)
  assert_eq(@spectral.check_spectral_tracedet(a, 7), true)
  // 不可對角化：Jordan 塊 [[1,1],[0,1]] 的譜分裂但特徵空間只有 1 維
  let jb = @core.mat_from_rows([[1, 1], [0, 1]])
  let (s2, d2) = @spectral.check_diagonalizable(jb, 7)
  assert_eq(s2, true)
  assert_eq(d2, false)
  assert_eq(@spectral.spectrum_roots(jb, 7), [(1, 2)])
}

///|
/// [T-Spec-Hyper] 超結構的「單元格大小矩陣」譜：把超化與譜化接起來。
///   區間超結構的 M[a][b] = |a⋆b| = |a−b|+1，其 χ 與直接由公式乘出的多項式一致。
test "hyper cell-size matrix spectralizes the interval hyperstructure" {
  let m = @spectral.hyper_cell_matrix(@hyper.interval_hyper(4))
  // M 的第 (a,b) 元素 = |a−b| + 1
  let mut ok = true
  for a = 0; a < 4; a = a + 1 {
    for b = 0; b < 4; b = b + 1 {
      let d = if a > b { a - b } else { b - a }
      if @core.mat_get(m, a, b) != d + 1 {
        ok = false
      }
    }
  }
  assert_eq(ok, true)
  let chi = @spectral.char_poly(m, 10007)
  assert_eq(@spectral.check_cayley_hamilton(m, 10007), true)
  assert_eq(@spectral.check_char_poly_coeffs(m, 10007), true)
  // 跡 = Σ M_aa = 4（每個對角元都是 0+1）
  assert_eq(@spectral.mat_trace(m), 4)
  assert_eq(chi.length(), 5)
}

///|
/// [T-Spec-Split][T-Spec-Chi] 譜分裂判準與手徵算子譜的符號表。
///   γ_*² = s·I，s = (−1)^{d(d−1)/2}：d ≡ 0,1 → +I；d ≡ 2,3 → −I。
///   故 d = 2,3 時 `sq1` 為 false、d = 4 時為 true；d = 3 時 γ_* 為純量 ⟹ 只有一個相異根。
test "spectrum split flag and chirality spectrum signs" {
  assert_eq(
    @spectral.spectrum_split(
      @spectral.spectrum_of(@core.mat_from_rows([[1, 2], [2, 4]]), 7),
    ),
    true,
  )
  // x² + 1 在 F₇ 上不可約（7 ≡ 3 mod 4）⟹ 不分裂
  assert_eq(
    @spectral.spectrum_split(
      @spectral.spectrum_of(@core.mat_from_rows([[0, -1], [1, 0]]), 7),
    ),
    false,
  )
  let (sp2, sq2, r2) = @spectral.chirality_spectrum(2, 5)
  let (sp3, sq3, r3) = @spectral.chirality_spectrum(3, 5)
  let (sp4, sq4, r4) = @spectral.chirality_spectrum(4, 13)
  let (sp7, sq7, r7) = @spectral.chirality_spectrum(2, 7)
  let (spx, sqx, rx) = @spectral.chirality_spectrum(2, 3)
  assert_eq(sp2, true)
  assert_eq(sq2, false) // s = −1
  assert_eq(r2.length(), 2)
  assert_eq(sp3, true)
  assert_eq(sq3, false) // s = −1，但 γ_* 是純量
  assert_eq(r3.length(), 1)
  assert_eq(sp4, true)
  assert_eq(sq4, true) // s = +1（d = 4 ⟹ d(d−1)/2 = 6 偶）
  assert_eq(r4.length(), 2)
  assert_eq(sp7, false) // −1 非二次剩餘 ⟹ 不可約
  assert_eq(sq7, false)
  assert_eq(r7.length(), 0)
  // p ≡ 3 (mod 4) 時連 Clifford 代數都建不起來：必須誠實回 false
  assert_eq(spx, false)
  assert_eq(sqx, false)
  assert_eq(rx.length(), 0)
}
