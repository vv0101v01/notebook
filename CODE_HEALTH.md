# CODE_HEALTH —— 代碼健檢 / 除錯 / 去重 / 減債 / 清死碼

對象：`tensorlab`（MoonBit，`moon 0.1.20261023` / `moonc v0.10.17+d971670cd`，`preferred_target = "wasm"`）。
本檔只記錄**做法與可重跑的證據**；數學內容見 [`THEORY.md`](THEORY.md)，其中 §13 是缺陷清單的摘要表。

## 0. 一頁結論

本檔分兩輪：**第一輪**（§1–§4，66 項測試）與**第二輪**（§5，超化／譜化／賬本／五關係，101 項測試）。

| 指標 | 初版 | 第一輪後 | 第二輪後（現況） |
|---|---|---|---|
| `moon check` | 0 errors, 2 warnings | 0 errors, 1 warning | **0 errors, 0 warnings** |
| `moon test` | 62 passed | 66 passed | **101 passed** |
| 零引用 `pub` 項目 | 15 | 0 | **0**（新增 4 個套件後重掃） |
| 跨套件同名定義 | 0 | 0 | **0**（`evolve.Ledger` 已改名 `RowSet`，見 §5.3） |
| 同一數學運算的重複實作 | 域 ×2、矩陣 ×2 | 各 ×1（全走 `@core`） | 各 ×1 |
| 已知數值錯誤 | 3 | 0 | 0（第二輪又抓 2 個語義錯誤，見 §5.1） |
| 邏輯／陳述錯誤 | 1 | 0 | 0（第二輪抓 3 個：`nullity` 等式、`H^k` 恆真、`γ_*` 奇 `d` 公式） |
| 未測試的 `pub` API | 4 | 0 | 0 |

第一輪剩下的唯一警告（`nc/moon.pkg` 的 `core`）在第二輪已**真正修掉**：
`nc_test.mbt` 不再為一個亂數序列而匯入整個 `core`，改用 3 行確定性 LCG。

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

## 4. 重跑（第一輪，數字為當時狀態）

```sh
export PATH="$HOME/.moon/bin:$PATH"
cd tensorlab
moon clean
moon check          # 0 errors, 1 warning（nc/moon.pkg）
moon test           # Total tests: 66, passed: 66, failed: 0
moon run cmd/main   # 92 行報告
```

---

## 5. 第二輪：新四層（`hyper` / `spectral` / `ledger` / `relations`）的健檢

新增 4 個套件（+35 項測試）後**重跑全部掃描**，不是沿用第一輪的結論。

### 5.1 除錯：本輪抓到並修掉的 5 個真缺陷

| # | 缺陷 | 症狀 | 根因 | 修法 |
|---|---|---|---|---|
| 1 | `regular_rep_matrix` 元素取錯 | `tr ρ(e) = 2` 而非 `|G| = 4` | 把 cocycle 的**指數** `ω(a,b)` 當成矩陣元素，忘了取 `ζ^{ω}`；且參數名 `_p` 導致 `p` 未綁定 | 元素改 `@core.mod_pow(ζ, ω(a,b), p)`，參數 `_p → p` |
| 2 | `mat_trace` 語義被誤用 | 13 個隨機案例誤報（`[[2,4],[5,0]]`、`p=7`：`Σ=9 ≠ 2`） | `mat_trace` 回**未約化**的整數 Σ，卻被拿去和 `F_p` 值比較 | 新增 `mat_trace_mod(a,p)`；需要原始 Σ 的地方（`hyper_cell_matrix` 的 `tr = 4`）保留 `mat_trace` |
| 3 | `dual_rank_nullity` 陳述錯誤 | 對 `n×(n+1)` 矩陣直接回 `false` | 寫成「`nullity(A) = nullity(Aᵀ)`」——只有方陣成立 | 改為指標等式 `nullity(A) − nullity(Aᵀ) = cols − rows` |
| 4 | `dual_chain_cochain` 是同義反覆 | 恆回 `true`（無資訊） | `H_k` 與 `H^k` 用**同一組秩數**計算 | 上同調改用轉置矩陣獨立求秩，逐維度比較 |
| 5 | `radon_total_ratio` 是假命題 | 比值不恆定，測試失敗 | 在 ℤ 上比較 `(Σ(Rf), Σf)` 與 `(n+1, 1)`，忽略 `F_p` 約化 | 改為 `radon_total_relative`（`F_p` 中的**相對值**），並把 `Σf ≡ 0` 的前移交給型別：`Int32?` 回 `None` |

另有 2 個語義修正：
`χ_{γ_*}` 對**奇** `d` 的公式（`γ_*` 是純量 `√s`，只有 1 個相異根，不是 `(x²+1)^{m/2}`）；
以及「`rank ≤ 1 ⟺ Det = 0 ⟺ #decomp = 0` 等價類」的猜想被 6561 個張量否決（蘊含格只有 3 條單向箭頭，等價類 0 個）。

### 5.2 去重：新增層之間的重疊

| 檢查 | 結果 |
|---|---|
| 「關係導出」是否重寫了 `evolve.derive_relations` 的消元邏輯 | **否** —— `ledger.derive_into` 直接呼叫 `@evolve.derive_relations`；`relations` 只做「壓成整數列」 |
| 「賬本」是否與 `evolve.RowSet` 重複 | 兩者語義不同（雜湊鏈 vs 觀測矩陣）⟹ 只做**橋接** `ingest_rows`，不各自實作 append |
| 域運算／矩陣運算是否又手寫了一份 | **否**（`relations` 全走 `@core.rank_mod/mat_transpose/mk_field`；`spectral` 走 `@core.*` 與 `@radon`/`@gauge`） |
| 跨套件同名定義 | **0**（掃描通過）；`evolve.Ledger → RowSet` 見 §5.3 |

### 5.3 減債：命名債與依賴債

* **命名債**：`evolve` 的 `Ledger{rows}` 與新套件 `ledger` 的持久賬本同名而語義相反（一個會被「導出」改寫、
  一個是不可篡改的鏈）。同名是債 —— 已改為 `RowSet` / `rowset_of` / `rowset_len` / `rowset_with_const` / `rowset_rows`。
* **測試依賴債**：`nc_test.mbt` 為了 `rng_seed/rng_below` 匯入整個 `core`（10 個 `pub` 函式、含 Smith 標準形），
  使 `nc` 恆帶一條 `unused_package` 警告。改為測試內 3 行確定性 LCG ⟹ 依賴歸零、警告歸零、語義不變。
* **死碼**：`hyper.mbt` 的 `let _ = attain`（死變數，隨第一輪重構殘留）已刪；
  第二輪掃出的 4 個死變數一併清掉：`nc.mbt` 的 `let _ = rep`（迴圈計數器其實沒用到 → `_step`）、
  `let _ = medges`（→ `_medges` 模式）、`spectral.mbt` 的 `let _ = rem`（整除時餘式恆 0 → `_r`）、
  `twist_test.mbt` 的 `let av = [0, 0]; let _ = av`。
  保留的 `let _ = x.pop()` 是**語義必需**（`Array::pop` 回傳 `Option`，回溯時就是要把剛推入的元素丟掉）。
* 保留的長函式（債務已記錄、暫不拆）：`main`（303 行，13 個線性區段）、`smith_diagonal`（132 行）、
  `even_center_dim`（74 行）、`integer_relation`（80 行）。理由同第一輪：收益/風險比不佳。

### 5.4 這一輪「新 API 的測試債」怎麼還的

新增 4 個套件帶來 **112** 個新 `pub` 項目（hyper 28、spectral 35、ledger 25、relations 24）。政策是：**新 `pub` 必須被測試或報告呼叫**，否則刪。
結果：零引用 `pub` 項目維持 **0**；其中 5 個（`hyper_cell_profile`、`spectrum_split`、`chirality_spectrum`、
`omega_ell`、`omega_field`）原本只被文件引用，已各補一條測試 —— 掃描時它們曾是「死 API」。

### 5.5 重跑（第二輪）

```sh
export PATH="$HOME/.moon/bin:$PATH"
cd tensorlab
moon check          # 0 errors, 0 warnings
moon test           # Total tests: 101, passed: 101, failed: 0
moon run cmd/main   # 133 行報告（新增 4 個區段，數值即時重算）
```

逐包：core 10、tensor 12、nc 10、twist 8、radon 5、gauge 9、metric 6、evolve 7、hyper 7、spectral 12、ledger 7、relations 8。

---

## 6. 第三輪健檢（新增 8 個套件之後）

### 6.1 除錯（這一輪真正修掉的錯誤）

| # | 症狀 | 根因 | 修法 |
|---|---|---|---|
| 1 | `mono_mul` 全線 panic（`Array::at` 越界） | `adem(i,j)` 在 `k = 0` 時回傳長度 1 的項，程式卻取 `term[1]` | `let t1 = if term.length() > 1 { term[1] } else { 0 }`（`Sq⁰ = 1`） |
| 2 | `ext_table` 的 `Ext^{s,t}` 亂數（出現 `−7`） | 最小自由分解的 `A⁺K_s` 用了**前一步的**索引表 `prev_xa/prev_xv`（差一頁） | 改成逐步累積的 `prev_idx`，並以「目標度數 = `t − deg(a)`」重建 `W_s` |
| 3 | `Ext^{2,2}` 變成 0（應為 1） | 商空間取代表元時，只與「已選代表」比主元，不與 `W` 的**行階梯**化簡 | 新增 `f2_reduce_vec` / `f2_echelon`，先模 `W` 再模已選代表 |
| 4 | `Sq³` 消失證書看似「憑空假設」 | 原本把 `Sq³` 當外部輸入 | 改為 `sq3_vanishes(alg)`：由不穩定性公理 + `dim ≤ 5` 推出零算子，並把理由寫成註解 |
| 5 | AHSS 測試互相矛盾（未扭曲卻有微分） | 把「twist 類 = 0」誤傳成「基類索引 0」 | 拆成 `ahss_zero_ops` / `ahss_twist_ops` 兩個**語義不同**的構造子 |
| 6 | `page_next` 不消滅 1×1 微分 | 測試把靶放在 `q = j−1` 以外的格（`d_r` 的 q 位移被忽略） | 以 `page_target_q` 反推源靶位置；文件寫明雙次 `(r, 1−r)` |
| 7 | 凝聚張量同構測試 panic | `chain_func` 的矩陣方向與「`trans[n]: V_n → V_{n−1}`」相反，且列欄索引顛倒 | 重寫為正向系（`rows = dims[n+1]`），並在文件說明 lim/colim 兩側的意義 |
| 8 | 固態性缺口恆為 0（失去意義） | 把「離散目標」的 `Hom(Z[S]^■, −)` 誤當成逆極限 | 區分 `cond_hom_free_discrete`（lim，常數型）與 `cond_hom_solid_discrete`（colim，全部局部常數），缺口才非零 |
| 9 | 森林 site 的覆蓋族方向錯誤（用超集） | Grothendieck 覆蓋必須是**子物件**的族 | 改為「分量覆蓋」：森林由它的連通分量覆蓋 |
| 10 | `dtensor` 的 Tor 數全錯（算出 1 而非 C(2g,i)） | 只用**一份**自由分解算 `Tor = H_*(K ⊗ F_2)`，等於在算 `Ext` 那一側（`K` 本身是分解，故 `H_{≥1}(K)=0`） | 改成兩份分解 `K ⊗_A K'` 再 `⊗_A F_2`，並把「取常數項」的約化寫成真正的矩陣運算 |

### 6.2 去重

* `vstack`（`grotop`）與 `kron`（`ahss`）各自只留一份實作；`ahss_add_ops` 取代了三處手寫的逐項模加。
* `f2_reduce_vec` / `f2_echelon` 是 `adams` 內唯一的 F₂ 消去路徑，原本三段重複的行階梯迴圈全部改呼叫它。
* `xops.alg_sum` 直接複用 `@ahss.alg_skeleton` / `alg_set_cup` / `alg_get_cup`，不重寫代數骨架。
* `xops.mask_popcount` 與 `forest_components` 共用同一個並查集 `uf_find`。

### 6.3 減債

* `ss.Page` 的雙次約定原本散落在 `page_next` / `page_hom_dim` / `page_im_dim` 三處；
  現在統一由 `page_dq` / `page_target_q` / `page_source_q` 三個函式提供，`qflip` 只在一處被讀。
* `adams.ext_table` 的迴圈原本是「先建 `W` 再建代表元」兩趟；現在 `W` 按目標度數分桶（`wbasis_by_deg`），
  避免每格重算，並讓 `Ext` 的定義（`dim K_s − rank W_s`）在第一眼可見。
* `grotop.Topology` 同時保存 `cov`（飽和 sieve，供公理）與 `fams`（登錄族，供層條件）：
  這個「兩份資料」是刻意的，因為公理檢查需要飽和結果、而層條件只需在一組基上檢查（文件已寫明）。

### 6.4 清死碼

* 刪除 `adams` 的 `admissible_basis`（內含意義不明的 `rec` lambda）、`idx_prev_get`、`ext_table` 第一個 no-op `rep` 迴圈。
* 刪除 `grotop.sheaf_check` 的 `blocks`/`idx` 變數、`xops` 的 `idx` 查表（`site_index` 直接遞增計數）、
  `ahss.alg_tensor` 第一趟沒有寫入的「目標枚舉」迴圈。
* 掃描方式：`grep -n "let _" */**.mbt`，逐條判斷是「語義必需」（如 `Array::pop` 回傳 `Option`）或真死碼；
  本輪掃到的 11 處之中 9 處刪除、2 處保留並加註理由。

### 6.5 重跑

```sh
export PATH="$HOME/.moon/bin:$PATH"
cd tensorlab
moon check          # 0 errors, 0 warnings
moon test           # Total tests: 144, passed: 144, failed: 0
```

逐包：core 10、tensor 12、nc 10、twist 8、radon 5、gauge 9、metric 6、evolve 7、hyper 7、spectral 12、
ledger 7、relations 8、**cellcx 3、ss 5、serre 4、adams 5、grotop 6、condensed 5、ahss 6、dtensor 4、xops 5**。

---

## 7. 第四輪健檢（規範形化之後）

### 7.1 除錯

| # | 症狀 | 根因 | 修法 |
|---|---|---|---|
| 1 | `canon` 整包編譯不過（`Array<Int32>` 解析失敗 20+ 條） | 撰寫時把 `Array[...]` 誤打成 `Array<...>`；`Array` 是**型別別名**，不是泛型構造子 | 寫了一支括號正規化腳本（巢狀 `Array<Array<…>>` 正確展開），並在每批寫檔後掃 `Array<` 殘留 |
| 2 | 巢狀 `Array[Array[Int32]]` 反覆退化成 `Array[Array[Int32]>` | 同上，`]]` 被吃掉一個 | 正規化腳本改成「迭代到不動點」，並用 `grep -c "Array<"` 當守門條件 |
| 3 | `@core.det_mod(pm, p)` 型別錯誤 | `det_mod` 的參數是 `Field` 不是 `Int32` | 改 `det_mod(pm, @core.mk_field(p))` |
| 4 | HNF 測試斷言 `[6,9]` 應化成 `[3,0]` 但得到 `[6,9]` | **測試前提錯**：單列的格就是 `Z·(6,9)`，化成 `[3,0]` 會改變格；gcd 只在**不同列之間**出現 | 改測「同格的不同生成集」與「`±` 正規化」 |
| 5 | 二面體 Burnside 給出 `4 ≠ 3` | **測試前提錯**：Burnside 只對 **G-不變的族**成立，而我挑的邊集族在 D₅ 下不封閉 | 改成在 D₅ 下封閉的族（所有單邊 + 所有兩兩邊組合）後一致 |
| 6 | 超結構「重標號」測試假通過 | 用**自同構**重標號時，交換群的乘法表逐項不變（內自同構平凡） | 改用**非自同構**置換 `σ(i)=i+1` 造同構副本 |
| 7 | 分次代數秩剖面測試失敗（剖面全變 1） | 我造的 `P = I + E₀₁ + E₁₀` 在 F₂ 上**行列式為 0**（不是換基） | 改用剪切 `I+E₀₁`（det=1）與 3-循環置換（det=+1），並加 `det_mod = 1` 斷言 |
| 8 | 凝聚鏈換基測試 panic／Smith 亂掉 | 源端維度是 4，卻用 2×2 的 `P` | 源端改用 4×4 剪切 |
| 9 | 胞腔複形測試 panic | `cx_sphere(2,7)` 的 `∂₂` 是 0×1（空矩陣），取 `data[0]` 越界 | 改用 `cx_lens(5,1,7)`（邊界非零），且只做整數么模（×(−1)）變換 |
| 10 | 軌道大小總和 20 ≠ 16 | `orbit_size_conj` 數的是「置換的個數」而不是「相異共軛矩陣的個數」 | 加去重（依展平鍵），總和回到 16 |

### 7.2 一條方法論判準（寫進 THEORY §28.4）

> **當定理與測試衝突時，先查測試的前提。**
> 第 4、5、6 條全部不是程式錯，而是「我以為的等價關係」比真正的等價關係更粗/更細。
> 這正好說明規範形的價值：它把「等價」寫成可執行的一行 `==`，讓錯誤前提立刻暴露。

### 7.3 去重與減債

* 排序邏輯統一：`moved_flat`（二面體）與 `canon_records` 共用插入排序寫法；`lex_cmp` / `lex_less` 是唯一的比較器。
* `canon_hyper` / `canon_hyper_iso` 共用成員表走訪；`canon_metric` 直接複用 `canon_graph`（距離矩陣與鄰接矩陣的置換作用相同）。
* `canon_page` 用 `canon_rref`，`canon_poset` 用 `canon_graph`，`canon_cx` / `canon_chain` 用 `smith_diagonal` —— 三者都是既有引擎，沒有重寫一次消元。

### 7.4 重跑

```sh
export PATH="$HOME/.moon/bin:$PATH"
cd tensorlab
moon clean && moon check     # 0 errors, 0 warnings
moon test                    # Total tests: 163, passed: 163, failed: 0
moon run cmd/main            # 171 行（新增 §28 區段）
```

逐包：core 10、tensor 12、nc 10、twist 8、radon 5、gauge 9、metric 6、evolve 7、hyper 7、spectral 12、
ledger 7、relations 8、cellcx 3、ss 5、serre 4、adams 5、grotop 6、condensed 5、ahss 6、dtensor 4、xops 5、
**canon 19**。
