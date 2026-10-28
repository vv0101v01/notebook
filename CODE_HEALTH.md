# CODE_HEALTH —— 代碼健檢 / 除錯 / 去重 / 減債 / 清死碼

對象：`tensorlab`（MoonBit，`moon 0.1.20261023` / `moonc v0.10.17+d971670cd`，`preferred_target = "wasm"`）。
本檔只記錄**做法與可重跑的證據**；數學內容見 [`THEORY.md`](THEORY.md)，其中 §13 是缺陷清單的摘要表。

## 0. 一頁結論

| 指標 | 健檢前 | 健檢後 |
|---|---|---|
| `moon check` | 0 errors, **2 warnings** | 0 errors, **1 warning** |
| `moon test` | 62 passed（其中 4 個 `pub` 函式**從未被任何測試呼叫**） | **66 passed**（零引用 `pub` 項目 = **0**） |
| 零引用 `pub` 項目 | **15** | **0** |
| 同一數學運算的重複實作 | 域運算 ×2、矩陣運算 ×2（`gauge` 自帶一套） | 各 ×1（全走 `@core`） |
| 已知數值錯誤 | 3 個（Int32 溢位/截斷：`nc_tree_formula`、`hyperdet222`、`rank1_table`） | 0 |
| 邏輯錯誤 | 1 個（秩引擎的射影比較與係數） | 0 |
| 未測試的 `pub` API | 4 | 0 |

唯一剩下的警告是 `nc/moon.pkg` 的 `core` 匯入：`nc.mbt` 不用它，但 `nc_test.mbt` 用；
MoonBit 以「套件」為單位的匯入清單無法分檔案，移除即編譯失敗（已實測）。**保留是正確選擇，不是遺漏。**

## 1. 方法（可重跑）

1. **死碼掃描**：對每個 `pub fn/struct/enum/type/data/const` 統計全專案引用（`@pkg.name` 跨套件 + 套件內裸名），排除定義行本身。
2. **重複掃描**：同一個名字是否在多個套件各自定義；同一算式（如 `(a*b) % p`、`(v % p + p) % p`、`mat_*`）是否多處手寫。
3. **溢位審計**：找出所有「先乘後模」的算式，按 `p` 的上界 `safe_prime_bound() = 46337` 推算中間值位寬（`p² + p = 2,147,163,906 < 2³¹−1` 是安全邊界；`p³`、`p⁴` 不是）。
4. **測試缺口審計**：`pub` 但零呼叫的函式 ⇒ 對應定理「只有文件、沒有驗證」。優先**補測試**而不是刪除（僅在被取代時才刪）。
5. 每一步都 `moon check` + `moon test` 全綠才前進，最後以 `moon clean` 全量重建複驗。

## 2. 找到並修掉的問題

### 2.1 邏輯錯誤（最嚴重）

**`tensor` 有兩套互相矛盾的秩引擎。**

- `classify222` 走 `rank1_table` 的 base-p 編碼表，結果正確。
- `tensor_rank_brute` / `sum_search` 走「逐元素相等 + 只允許係數 `+1`」的搜尋：
  - `2·(u⊗v⊗w)` 與 `u⊗v⊗w` 是**同一個**秩 1 張量（射影等價），但兩者的座標陣列不相等 ⇒ 被判成秩 2；
  - 係數只能 `+1` ⇒ 要表示 `2A + 2B + 2C` 需要 6 項，超出 `rmax` ⇒ 回傳 `None`。
- 這個 bug **長期隱形**，因為唯一的 `[P-Subadd]` 測試只在 F₂ 上跑（F₂ 的係數只有 1）且 `check_subadditivity` 本身也零呼叫。

修法：合併成**單一引擎** `decompose(t, tab, rmax) -> Array[(類別索引, 係數)]?`：

- 係數 `k ∈ 1..p−1`（完整性）；
- 索引非遞減（消去 `r!` 個排列）；
- 葉節點用 `Rank1Table.flags[vec_code(...)]` 做 **O(1)** 的秩 1 判定（把指數爆炸換成 `(p−1)·|list|` 的分支）；
- 新增 `proj_scale(a, b, p)`：回傳 `λ` 使 `b = λ·a`，`λ` **由首個非零座標決定**。
  這一條本身是一個獨立 bug：第一版用座標 `0` 求比例，當類別代表的首座標是 `0` 時 `λ = 0`，
  於是「分解見證」算出來的項被乘成 0 —— 40 個隨機張量裡有 21 個重建失敗。
- `tensor_rank(t, tab, rmax) = |decompose(...)|`；`check_subadditivity(samples, tab)` 改用同一引擎。

結果：`[P-Subadd]`、`[Ax-Tens]`、「見證重建」三組新測試全綠，報告新增一行
`[D-Decomp] W 態的秩-1 見證 | 3 項，重建=true`。

### 2.2 數值錯誤（Int32 溢位 / 截斷）

| 位置 | 問題 | 臨界值 | 修法 |
|---|---|---|---|
| `nc_tree_formula` | `C(3n−3,n−1)` 以 Int32 計算後才除 | `n ≥ 16` | 全程 Int64，`n ≤ 22` 精確（`T(22) = 642312451217745`） |
| `hyperdet222` | 四個因子（皆 `< p`）先連乘才約化 | `p > 215` | 內部改 Int64，逐步 `red()` |
| `rank1_table` | `u[i]·v[j]·w[k] % p` 三重乘積 | `p > 1290` | 逐步 `fld_mul` 約化 |

三個都屬「潛伏型」：現有測試只用 `p ∈ {2,3,5,7}`，所以從未觸發。第一個已經**真的**回傳過負數
（`n=16 ↦ −28304573`），因為 `nc_tree_formula` 只被 `n ≤ 7` 的測試與報告呼叫。
現在 `nc` 多一條回歸測試，硬編 `n = 14..22` 的精確值。

### 2.3 重複實作（去重）

| 運算 | 原本 | 現在 |
|---|---|---|
| 矩陣加／縮放／相等／單位矩陣 | `gauge` 自帶 `mat_add`/`mat_scale`/`mat_eq`/`mat_ident`（4 個） | `@core.mat_add` / `mat_scale` / `mat_eq_mod` / `mat_identity` |
| 逐分量加／內積 | `core.vec_add`/`vec_dot`、`evolve.dot`、`radon` 手寫累加 | `@core.vec_dot`（`holds_mod` 直接呼叫） |
| 域運算 | `radon`/`tensor`/`evolve` 手寫 `(x*y) % p`、`(x−y) % p + p) % p` 共 30+ 處 | `fld_add/sub/mul/div/norm` |
| 秩引擎 | 2 套（見 2.1） | 1 套 |

`radon` 的 `check_total_weight` / `check_quad_identity` / `fourier` / `check_slice` 改寫後，
既去掉重複的取模算式，也讓每一乘積都落在 `p²` 以內（結構上不可能溢位，而不是「靠參數約定不溢位」）。

### 2.4 死碼（清死碼）

刪除的 `pub` 項目（掃描確認刪除前零引用、刪除後仍全綠）：

```
core:   ilcm, mat_set, mat_eq(精確版), vec_add, multiplicative_relation
tensor: t3_code, slice_rank_lower_bound, rank1_list, tensor_rank_brute, rank_decomposition, is_rank1_in
nc:     metric_from_points
metric: vr_betti
（私有）nonzero_vectors, sum_search, decomp_search, t3_size, proportional/normalize_raw(前輪)
```

順帶刪掉的還有：`tensor.mbt` 裡 `slice_rank_lower_bound` 留下的**空 banner 註解**、
`rank1_table` 的 `let n = 3` 死變數、`rank2_ordered_pairs` 的 `let _ = i`、
`core/moon.pkg` 只為已刪函式而存在的 `moonbitlang/core/math` 匯入。

反向處理（**不刪，改為被驗證**）：`t3_smul`、`t3_simple`、`check_subadditivity`、`decompose`
原本零呼叫，現在由 `[Ax-Tens]`、`[P-Subadd]`、`[D-Decomp]` 三條測試覆蓋 —— 文件聲稱的定理終於有測試。

## 3. 未做 / 已知殘留

* `cmd/main/main.mbt` 的 `main` 仍有 ~290 行（12 個區段）。它是線性報告產生器，
  拆成 12 個函式可讀性會更好，但會動到全部輸出點；本輪不動，理由是收益/風險比不佳。
* `core.smith_diagonal`（132 行）與 `core.integer_relation`（80 行）仍偏長，內部步驟已註解，
  暫不拆。
* 仍未做 `moon fmt` 之外的風格治理（本輪跑過 `fmt`，冪等且不改變輸出）。
* 沒有引入 property-based / fuzz 測試框架：所有定理仍以「有限模型完備枚舉 + 手寫證明概要」驗證
  （這個認識論立場寫在 THEORY.md 開頭）。

## 4. 重跑

```sh
export PATH="$HOME/.moon/bin:$PATH"
cd tensorlab
moon clean
moon check          # 0 errors, 1 warning（nc/moon.pkg）
moon test           # Total tests: 66, passed: 66, failed: 0
moon run cmd/main   # 92 行報告
```
