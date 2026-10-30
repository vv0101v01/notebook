///|
/// [T-Adem] 已知的 Adem 恆等式（全部由 `@adams.mono_mul` 算出，不是硬編）。
test "Adem relations" {
  // Sq¹Sq¹ = 0
  assert_eq(@adams.mono_mul([1], [1]).length(), 0)
  // Sq¹Sq² = Sq³
  let a = @adams.mono_mul([1], [2])
  assert_eq(a, [[3]])
  // Sq²Sq² = Sq³Sq¹
  assert_eq(@adams.mono_mul([2], [2]), [[3, 1]])
  // Sq²Sq³ = Sq⁵ + Sq⁴Sq¹
  let b = @adams.mono_mul([2], [3])
  assert_eq(b.length(), 2)
  let mut has5 = false
  let mut has41 = false
  for m in b {
    if m == [5] {
      has5 = true
    }
    if m == [4, 1] {
      has41 = true
    }
  }
  assert_eq(has5, true)
  assert_eq(has41, true)
  // Sq³Sq³ = Sq⁵Sq¹
  assert_eq(@adams.mono_mul([3], [3]), [[5, 1]])
  // 可容許性
  assert_eq(@adams.is_admissible([4, 2, 1]), true)
  assert_eq(@adams.is_admissible([2, 2]), false)
}

///|
/// [T-Trunc][T-Ext-1][T-Ext-Van] Ext_A(F_2,F_2)：對角線以下消失、Ext^1 = 不可分解元。
test "Ext over the truncated Steenrod algebra" {
  let al = @adams.stralg_truncated(8)
  // 不可分解元：度數 1、2、4、8（Sq³ = Sq¹Sq² 是乘積、Sq⁵ = Sq²Sq³、Sq⁶ = Sq²Sq⁴ …）
  let indec = @adams.indecomposable_degs(al)
  assert_eq(indec, [1, 2, 4, 8])
  let ext = @adams.ext_table(al, 3, 8)
  // Ext^{0,t}：只有 t = 0
  assert_eq(ext[0][0], 1)
  assert_eq(ext[0][1], 0)
  assert_eq(ext[0][4], 0)
  // Ext^{1,t} = 不可分解元的度數
  assert_eq(ext[1][1], 1)
  assert_eq(ext[1][2], 1)
  assert_eq(ext[1][3], 0)
  assert_eq(ext[1][4], 1)
  // 對角線以下消失
  let mut ok = true
  for s = 0; s <= 3; s = s + 1 {
    for t = 0; t < s; t = t + 1 {
      if ext[s][t] != 0 {
        ok = false
      }
    }
  }
  assert_eq(ok, true)
  // Ext^{2,2} = h_0²、Ext^{2,4} = h_1² 皆為 1
  assert_eq(ext[2][2], 1)
  assert_eq(ext[2][4], 1)
  // 【重要】Ext^{2,3} = 0：因為 h_0·h_1 = 0 在 Ext 中成立（文獻關係，見 THEORY §19.4）
  assert_eq(ext[2][3], 0)
  // h_0h_1² = 0 ⟹ Ext^{3,5} = 0；但 h_0³ = Ext^{3,3} = 1
  assert_eq(ext[3][3], 1)
  assert_eq(ext[3][5], 0)
}

///|
/// [T-Trunc] 截斷不改變低度數的 Ext：D = 8 與 D = 6 在 t ≤ 6 上一致。
test "truncation stability of Ext" {
  let e8 = @adams.ext_table(@adams.stralg_truncated(8), 3, 6)
  let e6 = @adams.ext_table(@adams.stralg_truncated(6), 3, 6)
  assert_eq(e8, e6)
}

///|
/// [T-Koszul] 對照組（Koszul 對偶）：A = E(Sq¹) = F_2[Sq¹]/(Sq¹²) 時
///   Ext_A(F_2,F_2) = F_2[h_0]（每個 (s,s) 恰好一維）。
///   這條測試證明「最小自由分解引擎」本身是對的 —— 否則 A 的 Ext 表不足採信。
test "Koszul duality: Ext over an exterior algebra is polynomial" {
  let ext = @adams.ext_table(@adams.stralg_truncated(1), 5, 5)
  let mut ok = true
  for s = 0; s <= 5; s = s + 1 {
    for t = 0; t <= 5; t = t + 1 {
      let want = if s == t { 1 } else { 0 }
      if ext[s][t] != want {
        ok = false
      }
    }
  }
  assert_eq(ok, true)
}

///|
/// [E-AdamsPage] Adams 頁：把 Ext 表轉成譜序列，並讀出各莖的 E_2 維數。
test "Adams page from Ext" {
  let ext = @adams.ext_table(@adams.stralg_truncated(8), 3, 8)
  let page = @adams.adams_page(ext, 2)
  assert_eq(@ss.page_dim(page, 1, 1), 1) // h_0
  assert_eq(@ss.page_dim(page, 1, 2), 1) // h_1
  assert_eq(@ss.page_dim(page, 2, 2), 1) // h_0²
  let stems = @adams.adams_stem_dims(page, 3, 8)
  // 莖 0 是 h_0-塔：1, h_0, h_0², h_0³（四維，h_0⁴ 度數 4 超出截斷）
  assert_eq(stems[0], 4)
  // 莖 1 只有 h_1（h_0h_1 = 0）
  assert_eq(stems[1], 1)
  // 莖 3 有 h_2 與 h_0³? 由計算得出
  assert_eq(stems[3] >= 1, true)
}
