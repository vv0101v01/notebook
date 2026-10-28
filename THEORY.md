# tensorlab —— 定義、公理、定理、算法與演變恆定關係

> 本檔是 `tensorlab`（MoonBit，穩定版 `moon 0.1.20261023` / `moonc v0.10.17`）的理論主檔。
> 標籤系統與程式碼中的文件註解一一對應：
> `[Ax-]` 公理／`[D-]` 定義與構造／`[P-]` 命題／`[T-]` 定理／`[C-]` 推論／`[E-]` 演算法／`[Inv-]` 演變下恆定關係。
> 每一條都可重算：
>
> ```
> export PATH="$HOME/.moon/bin:$PATH"
> moon check          # 全專案 0 errors；1 warning（nc/moon.pkg 的 core 只被 nc_test.mbt 使用）
> moon test           # Total tests: 66, passed: 66, failed: 0
> moon run cmd/main   # 印出本檔所有數值結論的即時重算報告
> ```
>
> **認識論約定（重要）**：本檔不用「無窮一般性」的語氣偽裝計算結果。
> 每條陳述標明它的根據是 *(a)* 手寫證明概要（一般性成立）、*(b)* 有限模型上的完備枚舉（在该模型內是定理）、
> 或 *(c)* 有界搜尋（本檔如實寫出範圍）。多數 `[T-]` 同時具備 (a) 與 (b)：證明概要給出結構，
> 有限計算把結構變成可執行、可反查的斷言。

---

## 0. 設計原理：以消元作為數學結構之間的「度量」

八個套件不是八個不相干的題目，而是同一個引擎的重複套裝：

```
core  ── 消元（F_p 線性代數、秩、零空間、Smith 標準形、整數關係）
  ├── tensor   張量   → 展平矩陣 → 秩下界；超行列式 = 消元不變量的多線性版本
  ├── nc       非交叉 → 區間 DP = 關於「交叉」這一禁止關係的消元（可行解集合的邊界矩陣）
  ├── twist    H²     → δ¹, δ² 矩陣的 rank/nullity（上同調 = 消元的商空間）
  ├── gauge    叢     → Clifford = twist 代數的具體表示；格點規範 = 商空間 #orbit 的計數
  ├── radon    積分幾何 → RᵀR = nI+J，反演 = 解一個 2 參數矩陣族（消元立即給出）
  ├── metric   度量   → Vietoris–Rips 的邊界矩陣 → Betti 數 = nullity − rank
  └── evolve   演變   → 資料行向量集的「整數零化模」= 一個消元問題（本檔 §9）
```

**核心觀察（本專案的方法論）**：一個數學結構被編碼成一對 `(M, p)`（資料矩陣與特徵），
它的「不變量」就是 `M` 的消元不變量：

| 結構 | 資料矩陣 | 不變量 = 消元的哪個量 |
|---|---|---|
| 張量 | 三個展平 `flatten_k(T)` | `max_k rank` → 秩下界 `[P-Flat]` |
| 扭曲群代數 | `d₂ : C² → C³`、`d₁` | `dim H² = nullity(d₂) − rank(嵌入 d₁)` `[D-H2]` |
| 格點規範場 | 邊界–點 incidence | `#orbit = #(ker F)` 型計數 `[T-Gauge-Moduli]` |
| Radon | `R`（點–線 incidence） | `rank R` ⟹ 單射性 `[T-Radon-Inj]` |
| 單純複形 | `∂_k` | `β_k = nullity ∂_k − rank ∂_{k+1}` `[D-Betti]` |
| 演變軌跡 | ledger 行陣 | `ker_ℤ(rows)` = 恆定關係的模 `[D-Derive]` |

最後一列是「記錄演變後仍成立的恆定關係 ⟹ 再導出定理與算法」的實作形式：
**恆定關係 = 資料的整數零化模**，因此它本身可由消元算出，而不是靠人猜。見 §9。

---

## 1. `core`：消元引擎與算術基底

### 1.1 有限域與字長約束

* **[Ax-Field]** `(F_p, +, ·)`：`fld_add/fld_mul` 滿足交換、結合、分配律，`fld_inv` 在 `F_p^×` 上定義；
  `p` 由 `mk_field` 給定，`is_prime` 以試除判定（`primes_up_to` 逐數試除）。
  代碼：`core/core.mbt` 的 `Field/mk_field/fld_*`。
* **[Inv-Word]（實作不變量／前提條件）**：`Int` 為 32 位元，所有乘法在約化**前**進行，故
  全程必須 `p ≤ safe_prime_bound() = 46337`（`(2^31−1)^{1/2}` 下取整的保守值）。
  本專案實際使用 `p = 5`（Clifford／格點）、`p = 3`（張量枚舉）、`p = 10007`（消元與度量）、
  `p = 10007`（Radon）、`p = 7`（切片定理需 `n | p−1`）。
  此約束是**假設**而非結論：所有定理陳述都以它為前提。
* **[P-Mod-Neg]**：wasm 後端上 `v % p` 對負 `v` 保留負號，故一律先 `fld_norm`（`((v%p)+p)%p`）。
  這是本專案踩過的真實陷阱，列為命題以免後續引用者再犯。

### 1.2 消元

* **[D-Gauss]** `gauss_jordan(m, f) → Gauss{rref, rank, pivots}`：模 `p` 的行簡梯形。
* **[E-Gauss]（算法）** 主元搜尋 → 行交換 → 主元反元 → 全列消去；複雜度 `O(rows·cols·min(rows,cols))`。
* **[T-Rank]（秩–零化度定理，實作級驗證）** `rank(m) + nullity(m) = cols`，
  其中 `[D-Null]` `nullspace_basis` 由自由變量單位向量回代得基底。
  驗證：對隨機矩陣（種子固定）逐一模驗 `m · v = 0` 且基底線性獨立。
* **[T-Solve]** `solve_linear` 回傳 `Some x` ⟺ `rank(A) = rank(A|b)`；`None` ⟺ 增廣矩陣秩增大。
* **[T-Det]** `det_mod` 以行約化累乘主元；`det(A) ≢ 0 ⟺ A` 可逆 ⟺ `rank = n`（枚舉驗證 `n ≤ 3`）。
* **[T-Transpose]** `rank(mᵀ) = rank(m)`（枚舉驗證）。

### 1.3 Smith 標準形與有限交換群

* **[D-SNF]** `smith_diagonal(m)`：在 ℤ 上做行列初等變換（不約化模 `p`）得對角列 `d₁, d₂, …`，
  滿足整除鏈 `d_i | d_{i+1}`，`0` 代表自由生成元。
* **[T-SNF]（定理）** `coker(m : ℤ^cols → ℤ^rows) ≅ ⊕ᵢ ℤ/dᵢ ⊕ ℤ^{free}`，且
  `d₁d₂⋯d_k = gcd(全部 k×k 子式)`（行列式因子刻畫）。
  **驗證**（`core` 測試 `[T-SNF]`、「SNF preserves determinant up to sign」）：
  - 古典例子 `[[2,4,4],[-6,6,12],[10,-4,-16]] → [2, 6, 12]`（逐元相等）；
  - 整除鏈對每個例子逐條檢查 `d[i+1] % d[i] == 0`；
  - 對 3 個例子（含 `diag(2,10,15)`、`diag(4,0,0/0,6,0/0,0,9)`、上面的 3×3）檢查
    `∏ dᵢ ≡ ± det (mod 10007)` —— 即單位變換保持行列式至符號，這是標準形的獨立交叉檢查。
* **[D-AbGrp]** `ab_from_presentation(relations)`：**同一個** Smith 標準形的直接翻譯，
  `AbGroup{torsion, free_rank}`；`ab_order` 對無限群回傳 `-1`（顯式標誌，不是近似）。
  測試事實（全部為本專案實算）：
  - `⟨(2,0),(0,3)⟩ ⟹ ℤ/2 ⊕ ℤ/3 ≅ ℤ/6`：`free_rank = 0`、`torsion = [6]`、`ab_order = 6`
    （CRT 合併由 `d₁ = gcd(2,3) = 1`、`d₂ = 6` 自動完成）；報告即時印出 `Z/6（order 6）`；
  - `diag(6,10,15) ⟹ torsion = [30, 30]`、`order = 900`，與行列式因子公式
    `d₁ = gcd(6,10,15) = 1`、`d₂ = gcd(60,90,150) = 30`、`d₃ = 900/(1·30)` 一致；
  - `[[6,0,0],[0,10,0],[0,15,0]]`（第 2、3 列成比例 ⟹ 秩不足）`⟹ free_rank = 1`、`order = -1`；
  - 無關係矩陣 `mat_make(0,3,0) ⟹ ℤ³`，`ab_show = "Z^3"` ✓。

### 1.4 整數關係的可決定性

* **[P-IntRel]** 給定向量 `x ∈ ℝ^n`、高度上界 `H`、容差 `ε`：meet-in-the-middle 搜尋
  `integer_relation(xs, n, H, ε)` 若回傳 `Some r`，則 `|r·x| < ε` 且 `r ≠ 0`（殘差由實作直接給出）。
  測試：`x = (1, √2, 2+√2)`、`H = 1024`、`ε = 10⁻⁷` ⟹ `residual < ε` ✓；
  該三元組唯一的原始整數關係是 `(2, 1, −1)`（`2 + √2 − (2+√2) = 0`）。
* **[D-Stable]／[P-Stable]** `find_stable_relations(series, n, H, ε)`：對**時間序列**（每步一列不變量）
  找在每一步都成立的關係 —— 這是 §9 `[E-Derive]` 的浮點版原型。
  測試資料 `[(1,3,−1), (2,5,−1), (7,11,3)]` 滿足 `c = 2a − b`，導出的係數與 `(2,−1,−1)` 成比例 ✓。

### 1.5 隨機數與可重現性

* **[E-Rng]** `Rng{state}`：`rng_seed(42)` ⟹ 確定性 LCG；`rng_below(n)`。
  測試「deterministic rng」斷言同一種子產生同一序列 ⟹ **本檔所有「隨機」實驗都可逐字重現**。
  固定種子清單（寫死在測試裡）：`core` 42、`nc`（匹配 DP 對拍）7、`tensor`（Kronecker 秩）20261028、
  `radon` 20261028 與 7331、`gauge`（格點隨機規範場）4242、`evolve` 各驅動器的種子由呼叫給出
  （翻轉族 11 / 12、規範流族、剪切族等）。改變種子即改變樣本，但**不改變任何定理的結論**，
  因為每條 `[Inv-*]` 都在其後被轉移到獨立資料族上重新檢驗（§9）。

---

## 2. `tensor`：張量積、展平、超行列式

### 2.1 定義

* **[D-Tens]** `Tensor3{d0,d1,d2,data}`（F_p 上 `d₀⊗d₁⊗d₂`），`t3_of` 以 `(i,j,k) => 值` 構造。
* **[Ax-Tens]** 多線性：`t3_add`、`t3_smul` 逐分量；_simple_（秩 1）張量為 `u⊗v⊗w`（`t3_simple`）。
* **[D-Flatten]** `t3_flatten(t, mode)`：沿第 `mode` 模展平為 `(d_mode × d_others)` 矩陣 ——
  **這是張量理論接入消元引擎的唯一入口**。
* **[D-Decomp]** `decompose(t, tab, rmax)`：**唯一的**秩引擎。回傳 `[(類別索引, 係數)]` 使 `Σ 係數·list[i] = t`；
  索引非遞減（消去 `r!` 個排列），係數取 `1..p−1`（不只是 `+1`），葉節點用 `Rank1Table.flags` 的 O(1) 查表判秩 1。
  `tensor_rank(t, tab, rmax) = |decompose(...)|`。
  舊版 `tensor_rank_brute` 只允許係數 `+1` 且用逐元素相等判秩 1，會把 `2·(u⊗v⊗w)` 誤判成秩 2（已刪除，見 §13 缺陷表）。
* **[D-ProjScale]** `proj_scale(a, b, p)`：回傳 `λ` 使 `b = λ·a`（非同類則 0）；`λ` 由**首個非零座標**決定。

### 2.2 秩的下界與次加性

* **[P-Flat]** `rank(T) ≥ max_k rank(flatten_k T)`，因為秩 1 張量使每個展平的秩 ≤ 1。
  代碼：`flattening_lower_bound`。報告實值：GHZ 態 `= 2`，W 態 `= 2`（故兩者秩 ≥ 2）。
* **[P-Subadd]** `rank(A+B) ≤ rank A + rank B`：以同一引擎在 F₂ 的 144 個配對與 F₅ 樣本上枚舉驗證
  （`check_subadditivity(samples, tab)`）。
* **[P-KronRank]** `rank(A⊗B) = rank A · rank B`（矩陣的 Kronecker 積，作為張量積的退化情形）：
  `kron_mat` + `check_kronecker_rank_identity`（p=7）枚舉驗證。
* **[C-FlattenKron]（新推論）** 由 `[P-Flat]` + `[P-KronRank]`：
  `max_k rank flatten_k(A⊗B) = (max 展平秩 of A)·(max 展平秩 of B)`，
  故**張量積下 flattening 界相乘**。報告中以 `flattening_bound_of_product` 實算（p=7）。

### 2.3 Cayley 超行列式

* **[D-HyperDet]** `hyperdet222`：2×2×2 的 Cayley 超行列式，索引 `i*4 + j*2 + k`，
  25 項公式 = 4 個體對角線平方和 − 2×6 個面四次式 + 4×2 個「奇偶體對角」四次項。
  實值：`Det(GHZ) = 1`、`Det(W) = 0`。
* **[P-Shear]** `Det` 在每個因子的初等剪切（`SL₂`，det=1）下不變：`check_shear_invariance`。
  更强：`Det(g₀A,g₁B,g₂C) = (det g₀ det g₁ det g₂)²·Det(A,B,C)`，即 `SL₂³` 的**不變量**而非 `GL₂³` 的。
* **[T-DetSimple]（本專案的重要否決結果）** `Det` **不是**秩的不變量：
  在 `F₃` 上 `2×2×2` 張量中有 **864 個秩 3 而 `Det ≠ 0`**（同時秩 2 的也有 `Det ≠ 0` 者），
  所以「`Det ≠ 0 ⟹ 秩 = 3`」為假；正確的只能是其逆否命題的弱化形式。

### 2.4 `[T-Strassen-F3]`：F₃ 上 2×2×2 秩的完全分類（**新定理，由完備計算得出**）

對全部 `3⁸ = 6561` 個張量，以 `classify222`（`is_rank1` 的展平判準 + `rank1_table` 編碼表）判定秩，並精確計數
「無序秩 1 分解 `{u,v,w}+{u',v',w'}`」的個數 `#decomp`，得：

| 秩 | 個數 | `Det` | `#decomp`（無序、和為 T 的秩1分解數） |
|---|---|---|---|
| 0 | 1 | 0 | 0 |
| 1 | 128 | 0 | 0（本身即唯一分解） |
| 2 | 4032 | 0 或 ≠0 | **恰 1 或 ≥ 3；恆 ≠ 2** |
| 3 | 2400 | 0 或 ≠0 | 1..多 |

* **[T-Strassen-F3]（秩 2 的純組合判準）** 對 `T ∈ F₃²⊗²⊗²`：
  `rank(T) = 2` ⟺ `(Det(T) ≠ 0 ∧ #decomp(T) = 1) ∨ (Det(T) = 0 ∧ #decomp(T) ≥ 3)`；
  且對**所有** 6561 個張量 `#decomp(T) ≠ 2`。
  *幾何啟發（非本定理的依據）*：秩 2 的分解 `T = A + B` 等價於選取一條含 `T`、且兩端落在 Segre 簇上的直線；
  這些直線上的第二個交點給出一個對合，因此分解成對出現 —— 這解釋了為何 `#decomp = 2` 不會發生。
  **本定理的地位由完備枚舉（6561 例 × 全部 `(≤3)`-和的搜尋）給出**，不是由這段啟發式推得。
  代碼：`classify222`，`tensor` 測試 `rank 分類 = 1/128/4032/2400` 與 `#decomp ≠ 2`。
* **[L-Pair]** 無序計數 = 有序計數／2（`A+B` 與 `B+A` 成對）；用於 `rank2_decomposition_count`。

---

## 3. `nc`：非交叉樹、Catalan、associahedron

### 3.1 定義

* **[D-Chord]** `Chord{a,b}`：凸 `n` 邊形頂點間的一條弦（`a < b`）；`chords_cross` = 端點交錯。
* **[D-NCT]** 非交叉生成樹：`is_tree(n, es) ∧ is_noncrossing(es)`。
* **[D-Matching]** 非交叉完美匹配：`nc_perfect_matchings(m)`（`2m` 個頂點）。
* **[D-Tri]** `triangulations(n)`：全部三角剖分（對角線集合）。
* **[D-Dual]** `dual_graph`：三角形為頂點、共用對角線為邊。
* **[D-Flip]** `are_flippable/flip_degrees/flip_graph_connected`：對角線翻转與翻转圖。

### 3.2 計數定理

* **[T-NCT-Count]（Fuss–Catalan 型計數）** 凸 `n` 邊形的非交叉生成樹數
  `= C(3n−3, n−1) / (2n−1)`，值 `1, 1, 3, 12, 55, 273, 1428`（`n = 1..7`）。
  驗證：`nc_tree_formula`（公式，回傳 **Int64**）⟺ `count_nc_trees_brute`（完備枚舉，`n ≤ 6`）；整數性檢查到 `n ≤ 22`。
  `Int64` 是必要的：`n = 16` 時 `C(45,15) = 3.4×10¹²` 已超 `2³¹`，舊的 `Int32` 版本截斷後除以 `2n−1` 得到**負數**
  （`n=16 ↦ −28304573`）。現在 `n ≤ 22` 全部精確（`T(22) = 642312451217745 < 2⁶³`），回歸測試見 §10。
* **[P-NCT-Int]** `(2n−1) | C(3n−3, n−1)`：由計數的組合意義直接得證（Int64 精確枚舉到 n=22 全部通過）。
* **[T-Cat-Match]** `2m` 個頂點的非交叉完美匹配數 `= C_m`（Catalan），`m ≤ 6` 枚舉驗證。
* **[T-Tri-Cat]** 凸 `n` 邊形三角剖分數 `= C_{n−2}`，`n ≤ 8` 枚舉驗證。
* **[T-Cat]** `catalan_upto(7) = [1,1,2,5,14,42,132,429]`。

### 3.3 結構定理

* **[T-Dual]** 三角剖分的對偶圖是 `n−2` 個頂點、`n−3` 條邊、`maxdeg ≤ 3` 的**樹**。
  證明概要：連通（對角線圖連通）+ 邊數 = 點數 − 1 ⟹ 樹；一個三角形最多含 3 條對角線。
  驗證：`n ≤ 7` 全部剖分。
* **[T-Flip]** `n` 邊形的三角剖分翻轉圖是 `(n−3)`-正則且**連通**的圖（`n = 4..6` 完備驗證）。
  推論：任何剖分可在 `O(n²)` 步內翻到任何另一個 —— 這是 §9 `[E-Flip]` 漫遊的終止性保證。

### 3.4 最小權非交叉匹配算法

* **[E-MatchDP]（算法 `[D-MatchDP]`）** 區間 DP：
  `dp[i][j] = min over k ( w(i,k) + dp[i+1][k−1] + dp[k+1][j] )`，`dp[i][i−1] = 0`。
  正確性：非交叉性使頂點 `i` 的搭檔 `k` 把問題切成兩個獨立子區間（這是「非交叉」的**全部**用处）。
  複雜度 `O(n³)`，對比暴力枚舉的 Catalan 增長。
* **[T-MatchDP]（正確性定理）** `min_weight_nc_matching` 與 `min_weight_nc_matching_brute`
  在 `2m ≤ 12`、隨機對稱權（種子 7）上完全一致。
* **（已否決的推廣）** 同一套「兩函數區間 DP」**不**適用於最小權非交叉生成**樹**：
  樹的子結構在切割後不再獨立。本專案據此把 `[T-NC-Free]` 改走完全不同的路徑（見 3.5）。

### 3.5 `[T-NC-Free]`：單調圈距度量下 MST 不受非交叉約束（**新定理**）

設 `f : {1..n−1} → ℤ` 嚴格單調、`f(0)=0`，定義**圈距度量**
`w(i,j) = f(min(|i−j|, n−|i−j|))`（`cyclic_weights`）。則：

1. `[Ax-Metric]` `w` 是度量：`is_metric_w` 對 `f = [0,1,2,3,4]`、`[0,3,7,12,20]`、`[0,1,4,9,16]`
   與 `n = 4..6` 全部通過（三角不等式完備枚舉）；
2. **定理**：`w` 的最小生成樹權 = 非交叉生成樹的最小權 = `(n−1)·f(1)`，且兩者都由測地路徑
   （`C_n` 删去一條邊）達到。
   *證明*：每條邊的權重 `≥ f(1)`（因為任何兩點的圈距 `≥ 1`，`f` 單調），而任何生成樹有 `n−1` 條邊，
   故 `w(T) ≥ (n−1)f(1)`；長度全為 1 的邊構成 `n`-圈 `C_n`，删去任一條即得權重恰為 `(n−1)f(1)` 的生成樹，
   它是一條簡單路徑 ⟹ **無交叉** ⟹ 非交叉約束的下界同時可達。∎
   （推論：所有極小的樹都是「`C_n` 减一邊」，故 MST 不必交叉；`f` 非嚴格單調時可能出現其他最小樹，
   但它們同樣是 `C_n` 的子圖，故非交叉性仍成立 —— 本專案只對嚴格單調情形陳述。）
3. 算法形式 `[D-NC-Gap]`：`nc_freedom_gap(f,n) → (MST 權（Prim 算法）, NC 最小權（完備枚舉）)`，
   定理斷言兩者等於 `(n−1)·f[1]`。報告實值：`f = [0,3,7,12], n = 4 → (9, 9)`，`3·3 = 9` ✓。
4. **假設不可去（sharpness，`nc` 測試第 9 條）**：取 `n = 4`、`w` 為「兩條對角線 = 1、其餘四邊 = 5」，
   這是度量（`is_metric_w = true`），但 `MST = 7`（用兩條交叉對角線）而 `NC 最小 = 11`，
   `crossing_free = false`。故 `[T-NC-Free]` 的結論對**一般度量為假**，圈距單調性是實質假設。

## 4. `twist`：`H²(G, ℤ/ℓ)`、扭曲群代數與扭曲 K₀

### 4.1 上同調的消元定義

* **[D-Grp]** `Grp{orders}` = `ℤ/n₁ × … × ℤ/n_k`；元素以 `grp_code` 編碼為整數（`grp_of_code` 反編碼）；
  `[Ax-Grp]` 群公理由 `check_group_axioms` 完備枚舉驗證。
* **[D-Cochain]** 2-共鏈 = 函數 `G×G → ℤ/ℓ`，展平為 `var_count(g) = |G|²` 個坐標的向量，
  索引 `[D-VarIdx]` `var_index(g, ac, bc) = ac·|G| + bc`。
* **[D-Cob1][D-Cob2]** `d₁ : C⁰ → C¹`、`d₂ : C¹ → C²` 的矩陣表示（`d1_matrix`、`d2_matrix`）。
* **[D-H2]** `h2_compute(g, ℓ) → (dim C¹-im d₁ 計數, dim ker d₂, dim H², chain_ok)`；
  `dim H² = nullity(d₂) − rank(d₁|_{ker d₂})`，純消元。
* **[T-H2-Rank]** 鏈條件 `d₂ ∘ d₁ = 0`（報告輸出 `true`；這是 H² 有定義的前提，也是本專案發現並修正
  `d2_matrix` 中 cocycle 項符號錯誤的地方）。
* **[T-H2-Quot]** `H² = ker d₂ / im d₁`：對 `(ℤ/2)², ℓ=2` 完備枚舉全部 `2^16 = 65536` 個 2-共鏈，
  其中 `16` 個為上閉链；以 `cohomologous` 分堆得 `8 = 2^{dim H²}` 個類，每類大小 `2 = |B²| = ℓ^{dim B²}` ✓
  —— 這直接驗證了「商空間」的階，而不只是維數。

### 4.2 元素群的上同調維數（新定理：由計算發現、再給證明）

* **[T-H2-Elem]** `dim_{F_ℓ} H²((ℤ/ℓ)^k, ℤ/ℓ) = k(k+1)/2`。
  實算：`k = 1,2,3 → [1, 3, 6]` ✓（報告即時重算）；`(ℤ/3)², ℓ=3 → 3` ✓。
  *證明概要*：`H²(G,ℂ^×)` 由交替雙線型形式參數化；係數為 `ℤ/ℓ` 且 `G` 為初等 ℓ-群時，
  `ker d₂` 由「乘性」條件給出＝雙線型 + 對角自由，維數 `= (k choose 2) + k = k(k+1)/2`；
  `im d₁` 只消去對稱部分。本專案不用該論證反推，而是**先算出表、再用它检验實现**。
* **[T-H2-Cyc]** 循環群：`ℓ ∤ |G|` 時 `h1_dim = h2_dim = 1`（即 `H² = 0`，只剩常數 2-上閉链的計數約定）。
* **[T-H2-Kunn]** Künneth 型分解在 5 組 `(G₁,G₂,ℓ)` 上與直接消元一致。
* 數表（`twist/twist_test.mbt`，全部為消元實算）：`(ℤ/2)^{1..4}`、`(ℤ/3)^{1,2}`、`(ℤ/5)²`、
  `ℤ/4×ℤ/2`、`ℤ/4`、`ℤ/3×ℤ/9`。

### 4.3 扭曲群代數

* **[D-Omega]** `Omega{g, ℓ, p, w}`：以向量 `w`（长度 var_count）給出的 2-上閉链，取值於 `μ_ℓ ⊂ F_p^×`；
  `primitive_root(ℓ,p)` 取 `F_p^×` 中**恰為 `ℓ` 階**的最小元素 `ζ`（`ζ^ℓ = 1` 且 `ζ^j ≠ 1, j<ℓ`）；
  例：`primitive_root(2,5) = 4`、`primitive_root(4,5) = 2`。
* **[Ax-Cocyc]** `omega_is_cocycle(o)`：`ω(b,c) − ω(a+b,c) + ω(a,b+c) − ω(a,b) = 0`（乘法記號的對數形式）。
  報告：雙線型 `ω` ⟹ `true`。
* **[D-Aω]** 扭曲群代數 `A^ω = ⊕_{a∈G} F_p e_a`，`e_a e_b = ω(a,b) e_{a+b}`（`rho`/`mat_mul` 實現）。
* **[T-TwCenter]（定理）** `dim_{F_p} Z(A^ω) = |rad(b_ω)|`，其中 `b_ω(a,−)` 是 `ω` 的交替化雙線型型，
  `rad(b_ω) = {a : b_ω(a,−) = 0}`。
  *證明概要*：`z = Σ c_a e_a ∈ Z ⟺ ∀b: c_a(ω(a,b) − ω(b,a)) = 0 ⟺ c_a` 支撐在 `rad` 上；
  而 `rad` 上乘律退化成群代數 `F_p[rad]`，中心維數 `= |rad|`。
  代碼：`center_matrix`（線性條件組）→ `center_dim = nullity` ⟹ **這就是一個消元定理**；
  `omega_radical_size` 獨立計算 `|rad|`，兩者對 16 個上閉链全部相等（報告 `1 = 1`）。
* **[T-Tw-Square]（定理）** 若 `p ≡ 1 (mod ℓ)` 且 `ω` 取值於 `μ_ℓ`，則 `A^ω ⊗ \bar F_p ≅ Mat_d(F_p)^{⊕ r}`，
  `d² = |G| / |rad(b_ω)|`，`r = |rad|`。報告：`d² = 4`，`is_perfect_square = true`；
  對全部 16 個 cocycle 驗證。
  *證明概要*：`A^ω` 是中心單的 Azumaya 型代數；`rad` 是「退化根」，商 `G/rad` 上 `ω` 非退化 ⟹ 唯一
  忠實不可約表示維數 `d`，`d²·|rad| = dim A^ω = |G|`（Twisted group algebra 的標準事實在這裡以枚舉核實）。
* **[D-TwK0]／[T-TwK0]** 扭曲 K₀：`K₀^ω(G) ≅ ℤ^{|rad(b_ω)|}`（不可約 ω-表示的個數）。
  報告：`rank K₀ = 1`（此例 `|rad| = 1`）。代碼 `tw_k0_rank` 以 `rad` 大小給出，與 `[T-TwCenter]` 同源。
* **[T-Tw-Rank]（skew 秩偶性）** `b_ω` 為交替型 ⟹ `rank` 為偶數，`|rad| = ℓ^{k − rank}`；
  `check_skew_rank_formula` 在 `(ℤ/ℓ)^k` 的全部雙線型 `ω` 上驗證。

### 4.4 規範流（gauge flow）與不變量

* **[D-Gauge]** `omega_gauge(o, μ)`：`ω' = ω + δμ`，`μ : G → ℤ/ℓ`（1-共鏈）。
* **[T-Tw-Gauge]（定理）** 規範等價的 cocycle 給出同構的扭曲群代數：
  顯式同構 `φ(e_a) = ζ^{−μ(a)} e_a` 使 `φ(e_a e_b) = φ(e_a) φ(e_b)`。
  **不變量**：`rad(b_ω)`、`dim Z(A^ω)`、`rank K₀^ω` 沿 `[E-Gauge-Flow]`（遍歷全部 `μ`）不變。
  驗證規模：`(ℤ/2)²` 上 16 個 `ω` × 8 個 `μ`，報告輸出 `true / true`（不變量 + 顯式同構）。
* **[E-Coho]** `cohomologous(g,ℓ,u,v)`：`u − v ∈ im d₁`（再次是 rank 測試）。
  注記：`H²(G, μ_ℓ)`（本專案）不等於 `H²(G, U(1))`（拓撲群係數）；本檔只在有限 `μ_ℓ` 係數下陳述。

---

## 5. `gauge`：拉蒙場（Clifford 零模）與格點線叢

### 5.1 Clifford 代數＝具體的扭曲群代數

* **[D-Cliff]** `Cl_d` 由生成元 `γ_i` 與關係 `γ_i γ_j + γ_j γ_i = 2 δ_{ij}` 定義（`[Ax-Cliff]`）。
* **[D-Gamma]（構造算法／Jordan–Wigner）** 在 `F_p`（`p` 奇）上
  `γ_{2m-1} = Z^{⊗(m-1)} ⊗ X ⊗ I^{⊗…}`、`γ_{2m} = Z^{⊗(m-1)} ⊗ Y ⊗ I^{⊗…}`
  （`pauli_x/pauli_y/pauli_z`、`pauli_string`、`gamma_mats`）；
  `pauli_y` 回傳 `Int?`：**僅當 `p ≡ 1 (mod 4)`（`√−1 ∈ F_p`）時存在** —— 本專案取 `p = 1009`/`p=5`。
* **[T-Cliff]（定理的有限模型驗證）** 對 `d = 1..6`、`p = 5` 完備核對 `{γ_a, γ_b} = 2δ_{ab}·I`（報告 `PASS`）。
* **[D-SpinorDim]** `spinor_dim(d) = 2^{⌊d/2⌋}`；報告表 `[1,2,2,4,4,8]`（`d=1..6`）。
* **[T-Cliff-Twist]（橋接定理：拉蒙場是扭曲 K 理論的特例）** 令 `G = (ℤ/2)^d`，
  `ω(a,b) = Σ_{i>j} a_i b_j (mod 2)`（`clifford_cocycle_vec`），則映射 `ρ`（`rho`）滿足
  `ρ(a) ρ(b) = (−1)^{ω(a,b)} ρ(a+b)`，即 `Cl_d ≅ A^ω(G)` 作為 `F_p`-代數。
  報告：`d = 2..5` 全部通過（`check_clifford_is_twisted`）。
* **[T-Cliff-Center]（本專案的結構性結果）** 於是 Cl_d 的中心可由 §4 的中心消元**計算**：
  `dim Z = 1`（`d` 偶，`Cl_d ≅ Mat_{2^{d/2}}` 單純）、`= 2`（`d` 奇，`≅ Mat ⊕ Mat`），
  且 `dim Z = |rad(b_ω)|`、`spinor_dim(d)² · |rad| = |G|`。報告對 `d = 1..5` 逐條輸出
  「中心維數=預期 PASS / dim 關係 PASS」。
  這條把「向量叢／旋量」與「扭曲群代數中心」用**同一個算法**接了起來 —— 即本專案所要求的結構整合。
* **[T-Cliff-Chi]** 手徵算子 `γ_* = γ₁⋯γ_d` 滿足 `γ_*² = (−1)^{d(d−1)/2}`；報告 `PASS`（`d=1..6`）。
* **[T-Cliff-Kron]（Bott 週期性的構造版）** `Cl_d ⊗ Mat₂(F_p) → Cl_{d+2}`，
  `A ↦ A ⊗ X`、`B ↦ A ⊗ Z` 型映射保持 Clifford 關係；報告對 `d = 0..4` `PASS`。
  這給出 `Cl_{d+2}` 的**顯式**構造（不是存在性論證）。
* **[T-Cliff-Even]** `dim Z(Cl_d^{even}) = 2`（`d` 偶）／`1`（`d` 奇）；報告 `[2,1,2,1,2]`（`d=2..6`）——
  與 `dim Z(Cl_d)` 的奇偶規則恰好**互換**，這是偶代數中心算法的直接推論。

### 5.2 有限格點上的 `ℤ/ℓ` 線叢＝向量叢的離散模型

* **[D-Lat]** `Lattice{n, ℓ}`：`n×n` 環面格點，`lat_sites = n²`、`lat_edges = 2n²`（每點出 2 條邊）。
* **[D-Link]** 鏈變量 `u : Edges → ℤ/ℓ`；局部規範變換
  `[D-Gauge-Tr]` `(u^λ)(x→y) = u(x→y) + λ(y) − λ(x)`（`gauge_transform`）。
  「離散線叢」= 鏈變量模規範變換 —— 這是 `[D-H2]` 中 `C¹/B¹` 的同款構造，
  因此 **`twist` 的消元語言直接適用於格點規範場**。
* **[D-Curv]** `curvature(u)`：每個 plaquette 上四條邊之和有值 `F(p) ∈ ℤ/ℓ`。
* **[T-Gauge-Inv]（定理）** `F(u^λ) = F(u)`（報告 `check_curvature_invariant`）；
  且全場和 `Σ_p F(p) ≡ 0 (mod ℓ)`（**離散 Bianchi 恆等式**，`[T-Gauge-Bianchi]`）——
  每條邊恰屬於兩個 plaquette 且符號相反，故相加消去。這是把 Bianchi 恆等式写成一次可執行的邊界消元。
* **[T-Gauge-Hol]** 週途 `holonomies`（沿兩個獨立循環週途的和非平凡閉路）在規範變換下不變
  （`check_holonomy_invariant`）；平坦 ⟺ 全部週途為零 ⟺ `F = 0`（`is_flat`，在 `n ≤ 3` 完備枚舉中核對）。
* **[T-Gauge-Moduli]（模空間計數定理）** `n×n` 環面上平坦 `ℤ/ℓ` 線叢的個數與軌道數：
  `#flat = ℓ^{n²+1}`，`#moduli = #flat / ℓ^{n²−1} = ℓ²`。
  *證明概要*：`F : C¹ → C⁰(plaquette)` 線性，`ker F` 的餘秩 = plaquette 數 − 1（因為存在唯一線性關係
  「所有 plaquette 之和 = 0」）⟹ `#ker F = ℓ^{2n² − (n²−1)} = ℓ^{n²+1}`；
  規範群 `ℓ^{n²}/ℓ`（常數規範不起作用）作用自由 ⟹ 軌道大小 `ℓ^{n²−1}`。
  實算（報告）：`(n,ℓ) = (2,2) → 32 = 2⁵`、`#moduli = 4`；`(2,3) → 243 = 3⁵`、`#moduli = 9` ✓。
* **[T-Gauge-Moduli-Bij]（新的完全判準）** 軌道集 ⟶ 週途標號集是**雙射**：
  即「平坦鏈變量的規範軌道由它的兩個循環週途完全決定」（報告 `PASS；4（預測 4）`）。
  實作 `[D-Canon]`：`canonical_code` 把每條邊用 `gauge_transform` 規约成 `0`（沿生成樹），
  剩下的自由參數恰好是週途 —— 於是雙射不是論證而是**算法**（`check_moduli_bijective` 重數 `#distinct`）。
  此即離散版本的「flat connections ≅ Hom(π₁, A)」，對阿貝爾群 `ℤ/ℓ` 完備成立。

---

## 6. `radon`：離散 Radon 變換（有限幾何的積分）

* **[D-Radon]** `Radon{n,p}`：點集為 `ℤ/n × ℤ/n`（座標算術取 mod `n`），函數值在 `F_p`，故 `R` 是
  `n(n+1) × n²` 的 0/1 矩陣；`(Rf)(dir,t) = Σ_{q ∈ line(dir,t)} f(q)`
  （`line_points/line_count/radon_matrix`）。方向數為 `n+1`：`n` 個斜率 + 1 個鉛直（`dir = n`）。
* **[T-Radon-Gram]（定理）** `n` 為素數時
  `Rᵀ R = n·I_{n²} + J_{n²}`。
  *證明概要*：`(RᵀR)_{x,y}` = 同時含 `x` 與 `y` 的直線數。`x = y` 時有 `n+1` 條，對角元 `= n+1 = n + 1`；
  `x ≠ y` 時仿射平面內兩點決定恰 1 條直線，故非對角元 `= 1`。⟹ `RᵀR = (n+1)I + 1·(J − I) = nI + J`。
  報告：`n = 2,3,5,7` 全部 `PASS`（矩陣恆等式逐元核對）。
* **[T-Radon-Inj]** `rank R = n²`（`radon_rank` 給 `(n², 0)`）⟹ `R` 單射；前提 `p ∤ n(n+1)`（`[P-Radon-Cond]`）。
  **邊界情形（否定結果）**：`n = 4`（合數）時 `[T-Radon-Gram]` 失敗（報告 `PASS` 指「失敗已被確認」）——
  合數網格中兩點可決定多於一條「線」，故素數假設不可去掉。
* **[T-Radon-Inv]（顯式反演定理）** `(nI + J)^{-1} = (1/n)(I − J/(n²+n))`，於是
  `f = (1/n)·(RᵀR f − (Σ RᵀR f)/(n²+n) · 1)`，代碼 `gram_apply_inv`；
  `check_inversion` 在隨機 `f` 上核對 `(nI+J)^{-1} Rᵀ R f = f`（先約化再乘，避免溢出）。
* **[T-Radon-Quad]（新恆等式）** 對**任意** `f`（不需零均值）：
  `Σ_{lines} (Rf)² = n · Σ_x f(x)² + (Σ_x f(x))²`，且 `Σ Rf = n · Σ f`（`[T-Radon-Total]`）。
  *證明概要*：左 = `fᵀ(nI+J)f = n Σf² + (Σf)²`，直接由 `[T-Radon-Gram]` 得出 ——
  注意常見的「= n Σf²」只在零均值子空間成立；修正項 `(Σf)²` 是本專案明確寫出的版本。
  報告 `PASS`。
* **[D-Fourier]/[T-Radon-Slice]（切片定理）** `root_of_unity(n,p)`（需 `n | p−1`）給出 `n` 次本原根，
  `fourier(v,w,p)` 為 DFT；則 `F₁(Rf)(dir, ·) = F₂(f)|_{直線 ⊥ dir}` 逐點相等。
  驗證：`(n,p) = (2,5), (3,7), (5,11)`（報告 `PASS`）。
* **[E-Radon-Smooth]（算法）** 以 `R` 反覆做「線平均」平滑：`f ← R⁻¹(λ·(Rf) 的均值化)`；
  它是 §9 `[Inv-Radon]` 的演變驅動器。

---

## 7. `metric`：有限度量空間、Gromov–Hausdorff、Vietoris–Rips 同調

* **[D-MSpace]** `MSpace{n,d}`：`n` 點、整數距離矩阵；`mspace_cycle(n, step)` 造圈度量 `C_n`。
* **[Ax-Metric]** 度量公理（非負、`d(i,i)=0`、對稱、三角不等式）由 `check_metric` 完備枚舉驗證；
  `C₄`、`C₆` 通過，`(1,1,3)` 型三角被正確拒絕。
* **[D-GH]** 以**對應（correspondence）**定義 `2·d_GH(X,Y) = min_R dis(R)`，
  `R ⊂ X×Y` 為滿射對應，`dis(R) = max |d_X − d_Y|`。`gh2` 對 `n·m ≤ 16` 枚舉全部 `2^{n·m}` 個子集
  （超界回傳 `-1`，作為**顯式的範圍標誌**而非靜默失敗）。
  注記：因此 `gh2` 輸出是 `2 d_GH`（整數），本檔一律寫 `2·d_GH`。
* **[T-GH-Metric]** 在 3 點空間族上 `d_GH` 是真度量：對稱、三角不等式、`d_GH = 0 ⟺ 等距`
  （`check_gh_axioms`，報告 `PASS`）。實值：`2·d_GH((1,1,2),(2,2,4)) = 2`（= 直徑差，達到上界）；
  `2·d_GH((1,1,1),(2,2,2)) = 1`。
* **[T-GH-Lip]** `|diam X − diam Y| ≤ 2 d_GH(X,Y)`（`check_diam_lipschitz`）—— 1-Lipschitz 不變量的最簡例。
* **[T-GH-Sub]（新定理：子空間界）** 若 `Y ⊂ X` 且 `∀x ∃y∈Y: d(x,y) ≤ ε`，則 `2 d_GH(X,Y) ≤ 2ε`。
  *證明概要*：取對應 `R = {(x,y) : d(x,y) ≤ ε}`（满射），其 distortions 由 `d_X(x,x′) − d_Y(y,y′)`
  的不等式鏈控制，每步多出 `≤ ε`。實值：`2·d_GH(C₄, {0,1,2}) = 1`（`ε = 1` 時界緊）；
  `C₄{0,1,2}, C₄{0,2}, C₅{0,1,2}, C₅{0,3}` 全部 `PASS`。
* **[D-VR]** `vr_simplices(m, r)`：Vietoris–Rips（flag）複形 = 距離 `≤ r` 的**完全子圖**集合。
* **[D-Boundary]** `boundary_matrix(sims, dim)`：`F₂` 上的邊界算子 `∂_k`；
  `[T-Boundary²]` `∂_{k−1} ∘ ∂_k = 0`（在全部測試範圍內由 `check_euler` 的前置驗證覆蓋）。
* **[D-Betti]** `β_k = nullity(∂_k) − rank(∂_{k+1})`（`boundary_ranks`/`vr_betti_all`）—— 再一次是消元。
* **[T-VR-Euler]（定理）** `Σ_k (−1)^k f_k = Σ_k (−1)^k β_k`，對 `VR(C_n, r)` 的**全部** `r = 1..n`、
  `n = 4..8` 成立（`check_euler`；`alt_sum` 與 `vr_f_vector` 給出兩側）。
  注記：必須對**所有維度**求和 —— 截斷的同調無法支撐 Euler 恆等式（本專案曾據此否決一版測試）。
* **[T-VR-Cycle]（新定理：圈圖的 VR 完全計算）** `VR(C_n, r)` 的同調：
  `r = 1` 時為 `n`-圈（`β = (1,1,0,…)`，`n = 4..8` 完備），`r ≥ ⌊n/2⌋` 時是完整 simplex（`β = (1,0,…)`）。
  報告實值：`β(VR(C₆,1)) = [1,1,0,0,0,0]`、`β(VR(C₆,3)) = [1,0,0,0,0,0]`。
  注記：中間尺度 `1 < r < ⌊n/2⌋` 時 `β₁` 可以消失，故定理只在兩個端點給出精確斷言，
  中間尺度只驗證 Euler 恆等式（這是誠實的邊界）。
* **[T-VR-Fill]（邊界情形）** `n = 3, r = 1` 時 `VR` 已被填滿（`β₁ = 0`）—— 明確測試了定理的退化端。

---

## 8. 結構之間的不等式（「結構的度量」）

* **[P-Flat↔Det]** `max_k rank flatten_k(T) ≤ rank(T)`；`Det(T) ≠ 0 ⟹ rank ≥ 2`；
  但 `[T-DetSimple]` 說明反向不成立。於是 `Det` 給出的是**開集**（generic rank 3）的判準，
  而 flattening 給出**下半连续**的秩界 —— 兩者是不同的「度量」。
* **[P-Metric-Scale]** 本專案的 `d_GH` 用整數距離，`2 d_GH` 因此可精確計算（無浮點誤差）；
  `[T-GH-Sub]` 的上界與 `[T-GH-Lip]` 的下界在同一批資料上同時取等 ——
  這使 `d_GH` 在 3–4 點模型上成為可判定的精確量。
* **[C-Chain]** `core → (tensor | nc | twist | radon | metric) → gauge → evolve` 的依賴鏈是**單向**的：
  `gauge` 只用 `twist` 的中心算法表達 Clifford 的中心；`evolve` 只用各包的 ledger 提取器表達不變量。
  這保證「導出的關係」不會因循環定義而自證。

---

## 9. `evolve`：演變下恆定的關係 → 再導出定理與算法

### 9.1 帳本與導出算法

* **[D-Ledger]** `Ledger{rows}`：每行是某資料在演化過程中的一次觀測，欄位為該結構的整數不變量
  （`ledger_of`；若關係需要常數項則用 `ledger_with_const` 預置 `1` 欄）。
  `holds_exact` / `holds_mod` 對係數向量做逐點檢驗。
* **[D-Derive]（算法 `[E-Derive]`）** 從帳本**導出**恆定關係，而非假設它：
  1. 對 `rows` 在 `F_p` 上求零空間基底 `B = nullspace(rows, p)`；
  2. `normalize`：取絕對值最小代表元、除以 gcd、固定符號（得整數候選）；
  3. **先封閉再篩選**：把候選放進池（上限 64），做兩輪成對 `add_vec`/`sub_vec`；
  4. 保留 (a) 逐點通過（`exact ⟹ ℤ` 上檢驗，否則 `F_p`）且 (b) 提高 `F_p` 秩（`accepts`）者。
* **[T-Derive-Sound]（可靠性）** 第 4 步 (a)  ⟹ 輸出的每個向量都在全部觀測上成立。
* **[T-Derive-Complete-in-range]（範圍內完備）** 第 4 步 (b) ⟹ 輸出是 `F_p` 零空間的基底，
  故「任何在資料上成立的 mod-p 關係都在其 `F_p`-張成中」。
* **[P-Basis]（為何必須成對組合）** 消元給出的是**任意**基底，不是规範基：
  若某基底向量 `(2502, −1, 0, 0, 0)` 需要分母才能提升到 ℤ，它在 ℤ 上一定不合格；
  但兩個基底向量之差 `(0, 1, −1, 0, 0)` 就是真正的關係。
  **必須在過濾之前做成對加減**——這是本專案讓 `[T-Inv-Gauge]` 從失敗轉為成功的關鍵修正。
  同源的教訓：判斷「關係已被導出」要用**秩測試**，不能按「與目標成比例」比對。
* **[P-Transfer]／[T-Evolve-Stage]** `check_derived_then_transfer(a, b, p, exact, target)` 回傳
  `(在 A 上找到關係, target 在 B 上成立)`。第二個分量在**另一個資料族** `B` 上獨立檢驗 ——
  因此在 A 上僥倖成立的關係會被 B 拒絕。這是「恆定」與「僅是巧合」的分界。
* **[D-Rel-Derived]** `relation_derived(rels, target, p)`：`rank` 前後比較 ⟹ `target` 是否落在已導出的張成中。

### 9.2 五個演變族與五條恆定關係（`evolve_summary()` = 10/10）

| 演變 `[E-*]` | 帳本欄位 | 導出／轉移的 `[Inv-*]` 關係 | 實值 |
|---|---|---|---|
| `[E-Flip]` 三角剖分翻轉漫遊 | `(1, #△, V, E, Δ, #cross)` | `#△ = V`；`E = V − 1`（樹性）；`#cross = 0` | `n = 5 → 6` 轉移成立 |
| `[E-Gauge]` coboundary 規範流 `ω → ω+δμ` | `(|G|, |rad|, dim Z, d²·|rad|, Σω)` | `dim Z = |rad|`；`d²·|rad| = |G|`；`Σω` 守恆 | `d = 3 → 4` |
| `[E-Radon]` 線平滑迭代 | `(Σf², Σ(Rf)², (Σf)²)` | `Σ(Rf)² − 3Σf² − (Σf)² = 0`（目標 `[-3,1,-1]`） | 兩個不同 `f` 族（同 `n=3`） |
| `[E-Shear]` `SL₂` 剪切流 | `(Det T, Det T')` | `Det` 守恆（目標 `[-1,1]`） | `p = 3 → 5` |
| `[E-VR]` Vietoris–Rips 尺度增長 | `(1, χ_simplicial, χ_betti, β₀, β₁)` | `χ_simplicial = χ_betti`（目標 `[0,1,-1,0,0]`） | `n = 5 → 7` |

* **[T-Evolve-Summary]** `evolve_summary()` 對 5 個族各跑兩個階段（導出 + 轉移）⟹ `10 / 10` 通過（報告實值）。
* 報告中 `翻轉漫遊資料導出的恆等式條數 = 5`，係數基為
  `[3,-1,0,0,0,0]`、`[3,0,-1,0,0,0]`、`[2,0,0,-1,0,0]`、`[2,0,0,0,-1,0]`、`[0,0,0,0,0,1]`
  （欄序 `1,#△,V,E,Δ,#cross`）。前兩條之差即 `V − #△ = 0`，第一、三條之差即 `E = V − 1` ——
  **定理不是被塞進去的，而是從這組基的整數組合中讀出來的**。
  `n = 5` 時 `Δ ≡ 2` 是該 n 專屬的常數（`n = 6` 起 `Δ` 可取 3），所以它不會被轉移到 `n = 6`：
  這正是 `P-Transfer` 的作用。
* **[Inv-Word]（橫切前提）** 所有 `[Inv-*]` 陳述都只在 `p ≤ 46337` 的字長假設下有效（§1.1）。

### 9.3 由不變關係再導出的定理與算法

1. **定理**（`[T-Derive-Complete-in-range]` + `[P-Transfer]`）：若某關係在一個演變族的全部觀測上成立、
   且在第二個獨立族上成立，則它在「由該兩個生成過程連通的任何同型資料」上成立。
   對 `flip` 族 ⟹ 「翻轉不變 ⟹ 由連通性（`[T-Flip]`）得全部三角剖分不變」：
   `#△ = V`、`E = V−1`、`#cross = 0` 於是成为 `[T-Dual]` 的又一條獨立證明路徑。
2. **算法** `[E-Invariant-Discover]`（即 `derive_relations`）：任何能被寫成整數欄位帳本的結構，
   都能自動發現其守恆律；複雜度 = 一次 GF(p) 消元 + 常數倍的成對組合。
3. **算法** `[E-Gauge-Flow]`：把 §4.4 的 `μ` 當作優化方向，用 `[Inv-Gauge]` 作目標不變量 ——
   「沿規範流保持 `rad`」即是在 cocycle 空間上做正交投影的離散版本。
4. **算法** `[E-Radon-Smooth]`：`[Inv-Radon]` 的二次恆等式給出平滑迭代的能量守恆校驗器，
   可用來偵測實現錯誤（本專案正是靠它抓到 `Σ(Rf)²` 缺修正項的錯誤）。

---

## 10. 測試 ↔ 定理對照（66 項，全綠）

| 套件 | 測試數 | 覆蓋的主要標籤 |
|---|---|---|
| `core` | 10 | `[T-Rank] [T-Solve] [T-SNF] [P-IntRel] [Ax-Field]`（同包測試，可用私有欄位） |
| `tensor` | 12 | `[P-Flat] [D-Decomp] [D-ProjScale] [Ax-Tens] [P-Subadd] [T-Strassen-F3] [D-HyperDet] [P-Shear] [P-KronRank] [C-FlattenKron]` |
| `nc` | 10 | `[T-NCT-Count] [P-NCT-Int] [T-Cat-Match] [T-Tri-Cat] [T-MatchDP] [T-Dual] [T-Flip] [T-NC-Free]` |
| `twist` | 7 | `[T-H2-Rank] [T-H2-Elem] [T-H2-Cyc] [T-H2-Quot] [T-H2-Kunn] [T-TwCenter] [T-Tw-Square] [T-Tw-Gauge] [T-Tw-Rank]` |
| `radon` | 5 | `[T-Radon-Gram] [T-Radon-Inj] [T-Radon-Inv] [T-Radon-Quad] [T-Radon-Slice]` |
| `gauge` | 9 | `[T-Cliff] [T-Cliff-Twist] [T-Cliff-Center] [T-Cliff-Chi] [T-Cliff-Kron] [T-Cliff-Even] [T-Gauge-Inv] [T-Gauge-Bianchi] [T-Gauge-Hol] [T-Gauge-Moduli] [T-Gauge-Moduli-Bij]` |
| `metric` | 6 | `[Ax-Metric] [T-GH-Metric] [T-GH-Lip] [T-GH-Sub] [T-VR-Euler] [T-VR-Cycle] [T-VR-Fill]` |
| `evolve` | 7 | `[D-Derive] [T-Derive-Sound] [P-Transfer] [Inv-Flip] [Inv-Gauge] [Inv-Radon] [Inv-Shear] [Inv-VR] [T-Evolve-Summary]` |
| 合計 | **66** | `Total tests: 66, passed: 66, failed: 0` |

（每包計數以 `moon test --package username/tensorlab/<pkg>` 在**根目錄**執行為準；
在包目錄內執行 `moon test` 會跑整個專案，數字是累計值。）

**最終核驗（本專案交件狀態）**：`moon clean` 後重建 30 個 work items，
`moon check` → `0 errors, 1 warning`（`nc/moon.pkg` 的 `core` 只被 `nc_test.mbt` 使用，故在主建置中被視為未使用），
`moon test` → `Total tests: 66, passed: 66, failed: 0`；
逐包：core 10、tensor 12、nc 10、twist 7、gauge 9、radon 5、metric 6、evolve 7（合計 66 ✓）；
`moon run cmd/main` → 92 行報告，全部數值由本次執行即時算出。

---

## 11. 被計算否決的猜想（本專案的負面結果，全部可重算）

1. `Det(T) ≠ 0 ⟹ rank(T) = 3`：**假**。`F₃` 上 864 個秩 3、`Det ≠ 0` 的張量存在，
   秩 2 也有 `Det ≠ 0` 者 ⟹ `Det` 只是 `SL₂³` 的半不變量，不是秩不變量。
2. 「任意度量下 MST 必與非交叉約束兼容」：**假**（需要 `strict_monotone` 條件）——
   故 `[T-NC-Free]` 把條件明確寫進定理。
3. 「最小權非交叉生成樹可用兩函數區間 DP」：**假**（子結構在切割後不獨立），只有**匹配**版本成立。
3b. 「任何度量下 MST 都可取成非交叉」：**假**——`K₄` 上「對角線=1、邊=5」的度量給出 `MST = 7 < NC = 11`
   （見 §3.5 第 4 點，已寫成測試）。
4. 「`Σ_lines (Rf)² = n Σ f²` 對一切 `f` 成立」：**假**，缺 `(Σf)²`；零均值子空間上才成立。
5. 「`RᵀR = nI + J` 對任意 `n` 成立」：**假**，`n = 4` 反例（已寫成測試，`PASS` = 正確地失敗）。
6. 「3 點空間上 `2 d_GH` 總等於直徑差」：**假**（`(1,1,1)` vs `(2,2,2)` 得 `1` ≠ `2`）；
   只在 `(1,1,2)` vs `(2,2,4)` 這類達到上界。
7. 「截斷到 `k ≤ 2` 的同調可驗證 Euler 恆等式」：**假**，必須對全部維度求和。
8. 「隨機採樣 2-上閉链」：**不可行**（只有一個非零值的共鏈一般不是 cocycle）；
   本專案改用雙線型 `ω`（自動閉链）＋ `[Ax-Cocyc]` 驗證。
9. 「按與目標向量成比例判斷關係已導出」：**假**（基底是任意的）；改用秩測試。

---

## 12. 索引：符號 ↔ 代碼

| 符號 | 代碼位置 |
|---|---|
| 消元全部工具 | `core/core.mbt`（`gauss_jordan`, `rank_mod`, `nullspace_basis`, `solve_linear`, `det_mod`, `smith_diagonal`, `ab_*`, `integer_relation`, `Rng`） |
| 張量 | `tensor/tensor.mbt`（`t3_*`, `t3_flatten`, `flattening_lower_bound`, `decompose`/`decompose_search`, `tensor_rank`, `proj_scale`, `classify222`, `hyperdet222`, `kron_mat`, `rank1_table`） |
| 非交叉 | `nc/nc.mbt`（`nc_tree_formula`, `enumerate_nc_trees`, `catalan_upto`, `triangulations`, `dual_graph`, `flip_*`, `min_weight_nc_matching`, `cyclic_weights`, `nc_freedom_gap`） |
| 扭曲 | `twist/twist.mbt`（`d1_matrix`, `d2_matrix`, `h2_compute`, `h2_dim`, `mk_omega`, `omega_is_cocycle`, `center_dim`, `omega_radical_size`, `tw_irrep_dim_sq`, `tw_k0_rank`, `omega_gauge`, `check_gauge_invariance`, `skew_matrix`） |
| 叢／拉蒙 | `gauge/gauge.mbt`（`gamma_mats`, `check_clifford`, `clifford_cocycle_vec`, `rho`, `check_clifford_center`, `check_bott_periodicity`, `even_center_dim`, `mk_lattice`, `curvature`, `holonomies`, `canonical_code`, `flat_moduli`, `check_moduli_bijective`） |
| Radon | `radon/radon.mbt`（`mk_radon`, `radon_matrix`, `gram_matrix`, `gram_apply_inv`, `check_*`, `root_of_unity`, `fourier`, `check_slice`） |
| 度量 | `metric/metric.mbt`（`mspace_*`, `check_metric`, `gh2`, `check_gh_axioms`, `check_diam_lipschitz`, `check_subspace_bound`, `vr_simplices`, `boundary_matrix`, `boundary_ranks`, `vr_betti_all`, `check_euler`, `check_cycle_theorem`） |
| 演變 | `evolve/evolve.mbt`（`Ledger`, `ledger_of`, `ledger_with_const`, `derive_relations`, `relation_derived`, `check_derived_then_transfer`, `evolve_flips/gauge/radon/shear/vr`, `evolve_summary`） |
| 報告 | `cmd/main/main.mbt`（`moon run cmd/main`） |

---

## 13. 健檢：本輪發現並修掉的缺陷（每一項都有可重跑的證據）

| # | 缺陷 | 影響 | 修法 | 證據 |
|---|---|---|---|---|
| 1 | `sum_search` 以**逐元素相等**判秩 1，且只允許係數 `+1` | `2·(u⊗v⊗w)` 被判成秩 2：兩套「秩引擎」互相矛盾 | 改為單一引擎 `decompose`（係數 `1..p−1`、葉節點 O(1) 查表、射影比較） | `[P-Subadd]` 新測試 + 「見證重建」測試 |
| 2 | `proj_scale` 以**座標 0** 求比例 | 當類別代表的首座標為 0 時係數被算成 0，見證無法還原原張量 | 改用**首個非零座標** | 40 個隨機張量全部 `重建=true`（報告 `[D-Decomp]` 行） |
| 3 | `nc_tree_formula` 以 Int32 回傳 `C(3n−3,n−1)/(2n−1)` | `n ≥ 16` 時 `C` 超過 `2³¹`，截斷後除以 `2n−1` 得**負數**（`n=16 ↦ −28304573`） | 全程 Int64（`n ≤ 22` 精確） | `nc` 第 10 條測試；報告 `[T-NCT-Count] Int64` 行 |
| 4 | `hyperdet222` 內部用 Int32 連乘四個因子（可達 `p⁴`） | `p > ~215` 即溢位；由於測試只用 `p ∈ {2,3,5,7}` 而潛伏 | 內部改 Int64，逐步 `red()` 約化 | 全部 12 條 tensor 測試（含 `[P-Shear]` 對全 6561 個張量） |
| 5 | `rank1_table` 內 `u·v·w % p` 三重乘積 | `p ≥ 1291` 溢位（潛伏） | 逐步 `fld_mul` 約化 | 同上 |
| 6 | `radon`、`gauge`、`evolve` 各自手寫 `(x·y) % p`、`mat_add/mat_scale/mat_eq/mat_ident` | 與 `core` 的域運算重複（4 份實作），且手寫式在 `p → 46337` 時逼近溢位邊界 | 全部改走 `@core`（`fld_*`、`mat_add`、`mat_scale`、`mat_eq_mod`、`mat_identity`、`vec_dot`、`vec_scale`） | `moon check`/`moon test` 全綠；`cmd/main` 的既有數值逐字不變（只多了 2 行新證據） |
| 7 | 死碼：15 個零引用的 `pub` 項目（`ilcm`、`mat_set`、`vec_add`、`multiplicative_relation`、`t3_code`、`slice_rank_lower_bound`、`rank1_list`、`tensor_rank_brute`、`rank_decomposition`、`vr_betti`、`metric_from_points` …） | 維護負擔；其中 `[P-Subadd]` 的實作從未被任何測試呼叫（缺陷 1 因此長期隱形） | 刪除；被引用的改為**被測試覆蓋**（`t3_smul`/`t3_simple`/`check_subadditivity`/`decompose`） | 死碼掃描（0 個零引用項目）；測試數 62 → 66 |
| 8 | `core/moon.pkg` 匯入 `moonbitlang/core/math` 只為 `multiplicative_relation` | 刪掉該函式後成為未使用匯入 | 移除 | 警告數 2 → 1 |
