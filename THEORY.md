# tensorlab —— 定義、公理、定理、算法與演變恆定關係

> 本檔是 `tensorlab`（MoonBit，穩定版 `moon 0.1.20261028` / `moonc v0.10.17`）的理論主檔。
> 標籤系統與程式碼中的文件註解一一對應：
> `[Ax-]` 公理／`[D-]` 定義與構造／`[P-]` 命題／`[T-]` 定理／`[C-]` 推論／`[E-]` 演算法／`[Inv-]` 演變下恆定關係。
> 每一條都可重算：
>
> ```
> export PATH="$HOME/.moon/bin:$PATH"
> moon check          # 全專案 0 errors, 0 warnings
> moon test           # Total tests: 163, passed: 163, failed: 0
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

* **[D-RowSet]** `RowSet{rows}`：每行是某資料在演化過程中的一次觀測，欄位為該結構的整數不變量
  （`rowset_of`；若關係需要常數項則用 `rowset_with_const` 預置 `1` 欄）。
  ⚠️ 本輪改名：原稱 `Ledger`，與新套件 `ledger`（§17 的**持久**賬本）同名而語義不同 ——
  一個是「一次演變的觀測矩陣」，一個是「跨時間不可篡改的雜湊鏈」。同名是債，故 `Ledger → RowSet`、
  `ledger_of → rowset_of`、`ledger_len → rowset_len`、`ledger_with_const → rowset_with_const`。
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

## 10. 測試 ↔ 定理對照（101 項，全綠）

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
| `hyper` | 7 | `[T-Hyper-Rank] [T-Hyper-Interval] [T-Hyper-Trunc] [T-Hyper-Potency] [T-Hyper-Profile] [T-Hyper-Geodesic]`（§14） |
| `spectral` | 12 | `[T-CH] [T-TrDet] [T-Spec-TrDet] [T-Spec-Diag] [T-Spec-Conj] [T-Spec-Perm] [T-Spec-Radon] [T-Spec-Hyper] [T-Spec-Isospectral] [T-Spec-Chi] [T-Spec-Chi-Formula] [T-Spec-RegularRep]`（§15、§16） |
| `ledger` | 7 | `[T-Ledger-Det] [T-Ledger-Persist] [T-Ledger-Fork] [T-Ledger-Tamper] [T-Ledger-Audit] [E-Ledger-Bridge]`（§17） |
| `relations` | 8 | `[T-Rel-Scale] [T-Dual-Rank] [T-Dual-Chain] [T-Dual-Radon] [T-Dual-Tensor] [T-Contrast-Partition] [T-Impl-Matrix] [T-Ratio-Radon] [T-Ratio-Flip] [E-CollectInto]`（§18） |
| 合計 | **101** | `Total tests: 101, passed: 101, failed: 0` |

（每包計數以 `moon test --package username/tensorlab/<pkg>` 在**根目錄**執行為準；
在包目錄內執行 `moon test` 會跑整個專案，數字是累計值。）

**最終核驗（本專案交件狀態）**：`moon check` → **`0 errors, 0 warnings`**；
`moon test` → `Total tests: 101, passed: 101, failed: 0`；
逐包：core 10、tensor 12、nc 10、twist 8、radon 5、gauge 9、metric 6、evolve 7、hyper 7、spectral 12、ledger 7、relations 8
（合計 101 ✓）；`moon run cmd/main` → **133 行**報告，全部數值由本次執行即時算出。

`nc` 的唯一警告已清除：`nc_test.mbt` 曾為了一個亂數序列而匯入整個 `core`（測試依賴 ≠ 主建置依賴，
moonc 因此判 `core` 未被使用）。改法是在測試內用 3 行確定性 LCG 產生同一組權重 —— 依賴歸零，語義不變。

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
| 演變 | `evolve/evolve.mbt`（`RowSet`, `rowset_of`, `rowset_with_const`, `rowset_rows`, `derive_relations`, `relation_derived`, `check_derived_then_transfer`, `evolve_flips/gauge/radon/shear/vr`, `evolve_summary`） |
| 超化 | `hyper/hyper.mbt`（`hyper_from`, `hyper_classify`, `is_canonical_hypergroup`, `interval_hyper`, `truncated_add_hyper`, `tensor_rank_hyper`, `mat_rank_hyper_exhaustive`, `abs_diff_hyper`, `metric_hyper`, `flip_hyper`, `krasner_hyper`, `crisp_cyclic_hyper`, `hyper_potency`, `hyper_cell_profile`, `hyper_cell_size`） |
| 譜化 | `spectral/spectral.mbt`（`char_poly`, `mat_trace`/`mat_trace_mod`, `spectrum_of`, `spectrum_roots`, `check_diagonalizable`, `check_spectral_tracedet`, `check_trace_square`, `check_perm_char_poly`, `laplacian_of_graph`, `adjacency_of_graph`, `graph_diam`, `radon_gram_char_poly`, `isospectral_star_vs_cycle`, `chirality_matrix/spectrum`, `check_chirality_formula`, `regular_rep_matrix`, `check_regular_rep_trace`, `hyper_cell_matrix`, `check_spectral_conjugation`, `mat_inverse`, `projector`） |
| 賬本 | `ledger/ledger.mbt`（`Entry`, `Cell`, `Ledger`, `fnv1a`, `empty`, `append`, `observe`, `append_derived`, `entry_at`, `entries`, `verify`, `fork_index`, `corrupt`, `from_entries`, `observation_rows`, `derive_into`, `audit`, `replay`, `stats`, `ingest_rows`, `ingest_rowset`） |
| 五關係 | `relations/relations.mbt`（`Rec`, `rec_values`, `relative`, `relative_profile`, `check_relative_scale_invariance`, `dual_rank_nullity`, `dual_chain_cochain`, `dual_radon_injectivity`, `dual_tensor_permutation`, `contrast`, `contrast_counts`, `check_contrast_partition`, `implies`, `implication_closure`, `tensor_predicate_table`, `implication_matrix`, `equivalences`, `ratio`, `constant_ratio`, `radon_total_relative`, `flip_edge_vertex_ratio`, `collect`, `collect_into_ledger`） |
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

### 13.1 第二輪（超化／譜化／賬本／五關係）

| # | 缺陷 | 影響 | 修法 | 證據 |
|---|---|---|---|---|
| 9 | `regular_rep_matrix` 把 cocycle 的**指數** `ω(a,b)` 當成矩陣元素 | `tr ρ(e)` 得 `2` 而非 `|G| = 4`，`[T-Spec-RegularRep]` 直接失效 | 元素改為 `ζ^{ω(a,b)}`（`@core.mod_pow`）；參數 `_p → p`（原本 `p` 未綁定） | `spectral` 第 10 條測試：`tr = 4`、其餘 `0` |
| 10 | `mat_trace` 回傳**未約化**的整數 Σ，卻被拿去和 `F_p` 值比較 | 13 個隨機案例誤報（`[[2,4],[5,0]]`、`p=7`：`Σ=9 ≠ 2`） | 新增 `mat_trace_mod(a,p)`，`check_trace_square` 與 Radon 痕跡檢查改用它；`mat_trace` 保留「原始 Σ」語義（`hyper_cell_matrix` 的 `tr = 4` 需要它） | `spectral` 全部 12 條測試 |
| 11 | `C₅/p=7` 曾被當成 `[T-Spec-Lap-Cycle]` 的缺陷 | 其實是**前提** `n \| p−1` 不成立（`5 ∤ 6`），函式是對的 | 不改函式；把「誠實拒絕」寫成測試（`(5,7) == false`，並驗 `root_of_unity(4,5) = 2`） | `spectral` 第 4 條測試 |
| 12 | `dual_rank_nullity` 寫成「`nullity(A) = nullity(Aᵀ)`」 | 對長方形矩陣是**假**的（`n×(n+1)` 差 1）；第一次跑 `relations` 測試即被擋下 | 改為指標等式 `nullity(A) − nullity(Aᵀ) = cols − rows` | `relations` 第 2 條測試（`p ∈ {7,10007}`、`n = 2..4`） |
| 13 | `dual_chain_cochain` 用同一組秩數去算 `H_k` 與 `H^k`（恆真），且遺留 `let _ = transposed` 死碼 | 「對偶」變成同義反覆 | 上同調改用**轉置矩陣**獨立求秩（`rank_mod(mat_transpose(∂))`），三維度逐個比較 | `relations` 第 3 條測試：`C₄/C₅/C₆` 皆 `(∂∂=0, H^k=H_k)` |
| 14 | `radon_total_ratio` 拿**整數**比值 `(Σ(Rf), Σf)` 去和 `(n+1, 1)` 比 | 由於 `F_p` 約化，`(n+1)·Σf` 一般 `≠ Σ(Rf) mod p`，比值的「常數性」是假命題 | 改為 `radon_total_relative`：在 `F_p` 中取**相對值**；`Σf ≡ 0` 時回傳 `None`（把前提寫進型別） | `relations` 第 7 條測試（含零均值 `f` 的 `None` 案例） |
| 15 | `derive` 是保留字（解析錯誤 3002）；`while true { return … }` 在回傳 `Option` 的函式中報 4108 | 兩個檔案無法編譯 | `derive → append_derived`；`entry_at`/`entries` 改用 `let mut go = true` 迴圈 | `ledger` 7 條測試 |
| 16 | `evolve` 的 `Ledger` 與新套件 `ledger` 的 `Ledger` **同名不同義**（一個是觀測矩陣、一個是雜湊鏈） | 讀者與編譯器都會混淆；`analyze` 的重名掃描直接標紅 | 改名 `RowSet` / `rowset_of` / `rowset_len` / `rowset_with_const` / `rowset_rows` | 重名掃描：0 筆 |
| 17 | `nc_test.mbt` 為一個亂數序列導入整個 `core` | 測試依賴 ≠ 主建置依賴 ⟹ 恆有一條 `unused_package` 警告 | 測試內改用 3 行確定性 LCG | `moon check` → **0 errors, 0 warnings** |
| 18 | `hyper.mbt` 內 `let _ = attain` 的死變數；`cmd/main` 用 `impl` 當變數名（保留字） | 死碼 + 解析錯誤 | 刪除 `attain`；`impl → implm` | 死碼掃描 0 筆；`moon check` 全綠 |
| 19 | 舊稿 `χ_{γ_*} = (x²+1)^{m/2}` 對**奇** `d` 是錯的（`γ_*` 是純量 `√s`） | 手徵定理在 `d = 3` 時給出重根錯誤 | 依 `d` 奇偶分支寫定理，並加前置 `clifford_available(p)`；新增 `(3,5)`（1 個相異根）與 `(2,7)`（不分裂）的測試 | `spectral` 第 12 條測試 |
| 20 | 猜想「`rank ≤ 1 ⟺ Det = 0 ⟺ #decomp = 0` 為等價類」 | 6561 個張量算出：**三條單向蘊含**、等價類 **0** 個 | 不寫成等價；把反例方向寫進 §18.4 的蘊含矩陣 | `relations` 第 6 條測試（矩陣逐格比對） |

---

## 14. `hyper`：超化（把每個結構換成「可能的結果集」）

### 14.1 定義與公理

* **[D-Hyper]** 有限超結構 `Hyper`：`table[a * size + b][c]` 為真 ⟺ `c ∈ a ⋆ b`。乘積是**集合**，不是元素。
* **[D-Cell]** `|a ⋆ b|`（單元格基數）—— 超結構的全部資訊其實由「單元格尺寸矩陣」承載（見 §15.4）。
* **[Ax-Hyper]** 六條公理，全部寫成**可判定的謂詞**，而不是假設：
  1. **閉合** `check_closure`：每個 cell 非空；
  2. **結合** `check_assoc`：`triple_left = triple_right`，即 `⋃_{x∈a⋆b} x⋆c = ⋃_{y∈b⋆c} a⋆y`（比較**集合**）；
  3. **再生** `check_repro`：`∀a,b ∃x: b ∈ a ⋆ x`（「可除」）；
  4. **交換** `check_comm`：`c ∈ a⋆b ⟺ c ∈ b⋆a`；
  5. **么元** `check_identity(e)`：`e ⋆ a = {a}`（**恰好**是單點，不是「包含」）；
  6. **反元素** `check_inverse(e)`：`∀a ∃x: e ∈ a ⋆ x`。
* **[E-HyperClassify]** `hyper_classify(h, e)` 回傳六元布林向量 —— 於是「這是什麼代數結構」變成一次計算，
  而不是一段論述。**公理次序**（本專案全程引用）：(閉合, 結合, 再生, 交換, 么元, 反元素)。

### 14.2 由既有結構「超化」出的八族（判別表）

| 超化 `[D-*]` | 定義 | 六公理 | 結論 |
|---|---|---|---|
| `interval_hyper(n)` | `a ⋆ b = [min(a,b), max(a,b)]` | (T,T,T,T,**F**,T) | 結合、複製、交換都有；**無么元** ⟹ 非規範超群 |
| `truncated_add_hyper(r)` | `a ⋆ b = {c : c ≤ min(r, a+b)}` | (T,T,T,T,**F**,T) | 么元失效的原因：`0 ⋆ a = {0,…,a}` |
| `mat_rank_hyper_exhaustive(n,p)` | 由 `F_p` 上**實際**的矩陣秩資料建表 | (T,T,T,T,T,T) 〔`n=2, p=3`〕 | 規範超群（見 [T-Hyper-Rank]） |
| `tensor_rank_hyper()` | 張量秩版（載體 `{0,1,2,3}`，3 = 「≥3」） | (T,T,T,T,**F**,T) | 與截斷加法同型 |
| `metric_hyper(M)` | 有限度量圖的測地區間超化 | (T,T,T,T,**F**,T) | 測地凸性給出結合性 |
| `flip_hyper(n)` | associahedron 1-骨架（翻轉圖；`n=5` 時就是 `C₅`）的測地超化 | (T,T,T,T,**F**,T) | 與 `metric_hyper(C₄/C₅)` 同一個指紋 |
| `abs_diff_hyper(n)` | `a ⋆ b = {c : |a−b| ≤ c ≤ min(n, a+b)}` | (T,T,T,T,T,T) | 「能作差」⟹ 規範 |
| `krasner_hyper()` / `crisp_cyclic_hyper(n)` | Krasner 超域 / `ℤ/n` 的脆加法 | (T,T,T,T,T,T) | 正對照組 |

### 14.3 主定理

* **[T-Hyper-Rank]（本輪核心結論）** `mat_rank_hyper_exhaustive(2,3)` 與 `abs_diff_hyper(2)` **逐格相同**，
  且 `is_canonical_hypergroup` 為真。也就是說：
  > **矩陣秩的加法律就是絕對差–截斷和的區間律**：`rank(A+B) ∈ [|r−s|, min(n, r+s)]`。
  上界 `min(n, r+s)` 與下界 `|r−s|` 是古典的；**本輪新增的是「取盡性」** —— 區間內每一點都可達到，
  在 `2×2`、`F₃` 上逐格驗證（`|1 ⋆ 1| = 3`：消去與堆疊都發生）。
  兩條獨立路徑（純代數的秩枚舉 vs 純組合的區間公式）給出同一個表 ⟹ 不是巧合，是同一條律。
  佐證：`hyper_cell_size(mh, 1, 1) = 3`（`{0,1,2}`）——消去（0）與堆疊（2）在秩 1+1 時都會發生。
* **[T-Hyper-Interval]** 區間超化：`0 ⋆ 2 = {0,1,2} ⊋ {2}` 故么元不成立；但 `e ∈ a ⋆ 0` 恆成立，故
  「反元素」謂詞反而為真 —— **兩條公理不能互相代替**，必須各自判定。
* **[T-Hyper-Trunc]** 截斷秩超化：`|a ⋆ b| = min(r, a+b) + 1`，且 `0 ∈ a ⋆ b` 恆成立（「零在所有乘積中」）。
* **[T-Hyper-Potency]** 超冪次 `pot(a)` = 最小的 k 使 `a^(*k) = a^(*k+1)`（集合穩定）。
  實測：`truncated_add_hyper(3)` 在 `a = 1` 上為 `3`；`crisp_cyclic_hyper(n)`（`n = 2..9`）為
  `[2,3,3,4,4,4,4,5]` = `⌈log₂ n⌉ + 1` —— 即「反覆自乘把集合撐滿載體所需的步數」是對數級。
* **[T-Hyper-Profile]** 單元格尺寸剖面：`interval_hyper(4)` 的 `|a−b|+1` 分佈為 `[0,4,6,4,2]`
  （Σ = 16 = `|A|²`）；且秩超群與絕對差超群的剖面**逐格相同**。

### 14.4 算法（超化給出的新算法）

1. `[E-HyperClassify]`：把「這個結構是什麼」化為 `O(|A|³)` 的判定（`check_assoc` 用集合比較）。
2. `[D-Hyper-MatRank]`：由資料建超結構 —— **不需要先猜公式**，秩枚舉直接給出乘積表；再用
   `abs_diff_hyper` 對照，公式是「被發現的」而不是「被假設的」。
3. `[D-CellMatrix]`：單元格尺寸矩陣（§15.4）把超結構送進譜化管線。

---

## 15. `spectral`：譜化（每個結構換成「它的譜」）

### 15.1 工具箱

* `[E-CharPoly]` Faddeev–LeVerrier：`M_k = A·M_{k−1} + c_{n−k+1}·I`，`c_{n−k} = −tr(A·M_k)/k`。
* `[E-DivLinear]` 綜合除法（`(x−r)` 除多項式）；`[E-PolyMat]` 矩陣代入多項式（Horner）。
* **[D-Trace] vs [D-TraceMod]**：`mat_trace` 是**未約化**的整數 Σ；比對 `F_p` 值時必須用
  `mat_trace_mod`。本輪的真實缺陷：`[[2,4],[5,0]]`、`p = 7` 時 `Σ = 9 ≠ 2`，
  13 個隨機案例因此誤報 —— 參見 §13 的新增條目。

### 15.2 譜的基本定理（全部以隨機矩陣 + 有限域重算驗證）

| 標籤 | 陳述 | 驗證 |
|---|---|---|
| `[T-CH]` | `χ_A(A) = 0` | `p ∈ {7,11,13,17}`、`n = 2..4` 隨機矩陣 |
| `[T-TrDet]` | `cₙ₋₁ = −tr A`、`c₀ = (−1)ⁿ det A` | 同上（`check_char_poly_coeffs`） |
| `[T-Spec-TrDet]` | 譜分裂時 `Σλ = tr A`、`Πλ = det A` | `check_spectral_tracedet` |
| `[T-Spec-Diag]` | 可對角化 ⟺ 譜分裂 **且** `Σ dim ker(A−λI) = n` | `[[1,1],[0,1]]`：分裂=T、可對角化=**F**、`spectrum_roots=[(1,2)]` |
| `[T-Spec-Conj]` | `χ_{PAP⁻¹} = χ_A` | 置換 P 與剪切 P 各驗一次 |

### 15.3 具體譜

* **循環圖的 Laplace 譜**：`spec L(C_n) = {2 − ω^k − ω^{−k}}`，`ω` 為 `F_p` 中的 `n` 次本原根。
  成立：`C₃/p=7`、`C₄/p=13`、`C₅/p=11`；**不成立**：`C₅/p=7`（因為 `5 ∤ 6`）。
  這條定理寫明了前提 `n | p−1` —— 前提不是裝飾，去掉它命題就是假的。
  （附帶修正：`root_of_unity(4,5) = 2`，因為 `F₅^×` 中 2 的階正是 4；曾誤判為缺陷。）
* **[T-Spec-Perm]** 置換矩陣：`χ = Π_cycles (x^{len} − 1)`。在 `(3,2)`、`(2,2,1)`、全不動、4-循環上逐項相符。
* **[T-Spec-Radon]** Radon 的 Gram 算子 `RᵀR`（`n²×n²`）之 `χ` 由 `radon_gram_char_poly` 顯式給出（`n ≤ 3` 驗證）。
* **[T-Spec-Hyper]** `hyper_cell_matrix(interval_hyper(4))` 的元素為 `|a−b|+1`，
  `χ = [9987,9951,9967,10003,1] (mod 10007)`、`tr = 4`、`deg = 4` —— **超化 → 譜化**的直通車。
* **[T-Spec-Isospectral]** 譜不決定結構：`K_{1,4}` 與 `C₄ ⊔ K₁` 的**鄰接**譜相同（皆 `{±2,0,0,0}`，`p = 17` 時 `χ` 相同），
  但直徑是 `2` 對 `−1`（不連通）。**易錯點**：這兩者的 **Laplace** 譜其實不同 —— 用錯矩陣就會得到假反例。

### 15.4 手徵算子的譜（修正過的版本）

`γ_* = γ₁γ₂⋯γ_d`（`[D-Chirality]`，前提 `@gauge.clifford_available(p)`）。令 `s = (−1)^{d(d−1)/2}`，則

| `d mod 4` | `s` | `γ_*²` | `χ_{γ_*}` | `p = 5` | `p = 13` |
|---|---|---|---|---|---|
| 0, 1 | `+1` | `+I` | `(x² − 1)^{m/2}` | 分裂 | 分裂 |
| 2, 3 | `−1` | `−I` | `(x² + 1)^{m/2}`（**僅偶 d**） | 需 `p ≡ 1 (4)` | 需 `p ≡ 1 (4)` |

* **[T-Spec-Chi]** `d` **奇**時 `γ_*` 其實是純量 `√s·I` ⟹ `χ = (x − √s)^m`，只有 **1** 個相異根；
  舊稿的 `χ = (x²+1)^{m/2}` 對奇 `d` 是**錯的**。實測：`(3,5)` → 分裂、`roots = 1`；`(4,13)` → `γ_*² = I`（`sq1 = true`）、`roots = 2`。
* 前置條件：`p ≡ 3 (mod 4)` 時 `−1` 非二次剩餘 ⟹ `x²+1` 不可約 ⟹ 不分裂（`(2,7)` 驗證），
  且 `p = 3` 時 `clifford_available` 直接拒絕（無 `i` 的 `0` 回退）。
* **[T-Spec-Chi-Formula]** 顯式 `χ` 與 `char_poly` 逐係數比對（`p > 2d+2` 時）。

### 15.5 投影與跡

* **[D-Projector]** 冪等 `P² = P` ⟹ `spec P ⊆ {0,1}` 且 `tr P = rank P`。
  實測 `[[1,0],[0,1],[1,1]]`、`p = 7`：冪等、`tr = rank = 2`、`spectrum_roots = [(0,1),(1,2)]`。
* `projector(A)` = `A(AᵀA)⁻¹Aᵀ`，**前提：A 行滿秩**；秩虧時回傳 `None`（測試斷言 `None`，不靜默給錯答案）。

---

## 16. 正則表示：跡比譜更細

* **[D-RegularRep]** 扭曲群代數 `A^ω` 的左正則表示：`ρ_reg(a)[b][a+b] = ζ^{ω(a,b)}`。
* **[T-Spec-RegularRep]** `tr ρ_reg(e) = |G|`，`a ≠ e` 時 `tr ρ_reg(a) = 0`。
  實測 `G = ℤ/2 × ℤ/2`、`ℓ = 2`、`p = 5`、零 cocycle：`tr ρ(e) = 4 = |G|`，其餘 `0`。
* **命題（跡 vs 譜）**：`ρ_reg` 的**譜**在多數情況下把不同元素混在一起，而**跡**能分離單位元 ——
  所以「譜化」不是萬能的不變量提取器，這正是 §18 還要引入**五種關係**的原因。
* 缺陷記錄：`regular_rep_matrix` 曾把 cocycle 的**指數** `ω(a,b)` 直接當矩陣元素（應用 `ζ^{ω(a,b)}`），
  導致 `tr ρ(e) = 2` 而非 `4`；已改為 `@core.mod_pow(ζ, ω(a,b), p)`。

---

## 17. `ledger`：超級持久賬本

### 17.1 結構

* **[D-Entry]** `Entry{seq, kind, values, parents, prev, hash}`；`kind`：`0` 觀測、`1` 導出關係、`2` 定理宣稱。
* **[D-Cell]** 單向鏈（不可變）：`Nil | Node(Entry, Cell)` —— 追加只建新節點，**舊快照結構共享**。
* **[D-Ledger]** 頭：`{head, len, tip}`。
* **[D-Fnv]/[D-HashEntry]** FNV-1a 64；`hash = f(seq, kind) → values → 0 → parents → 1 → prev`
  （`0/1` 是欄位分隔符，避免「`[1,2]`+`[]`」與「`[1]`+`[2]`」撞雜湊）。

### 17.2 定理（全部可重跑）

| 標籤 | 陳述 | 驗證 |
|---|---|---|
| `[T-Ledger-Det]` | 同一串觀測 ⟹ 同一個 `tip`（重算 `seq` 連續、`prev` 連結、`hash` 相符） | `replay(rows)` 與原賬本 `tip` 相等 |
| `[T-Ledger-Persist]` | 追加不改變任何舊快照 | 3 → 5 條後，舊賬本逐位元不變、仍 `verify` |
| `[T-Ledger-Fork]` | `fork_index` = 共同前綴長度（以 `hash` 比對） | 3 條 → 5 條的延伸：`fork_index = 3` |
| `[T-Ledger-Tamper]` | 篡改任何一條（首、中、尾）必使 `verify = false` | 3 個位置各驗一次 |
| `[T-Ledger-Audit]` | 每條導出條目必須在**它的全部父條目**上成立 | `audit` 回傳 (通過, 失敗) = (n, 0) |

### 17.3 與演變／關係的橋

* **[E-Ledger-Bridge]** `ingest_rows(l, rows, kind)` / `ingest_rowset(l, rs, kind)`：把 `evolve` 的觀測列
  （或 `relations` 的 `rec_values`）整批入賬。**與逐條 `append` 得到同一條雜湊鏈**（同一 `tip`）、
  舊前綴不受影響（`fork_index` = 舊長度）、可 `replay`。
* `derive_into(l, p, exact)`：由入賬的觀測用 §9 的消元引擎導出恆定關係，寫成 `kind = 1` 且帶父節點的條目；
  `audit` 再逐條回驗。實測（`evolve_radon(3,10007,6,3)` 的 7 列）：導出 `1` 條、稽核 `1/0`。
* 由此得到一條**跨層命題**：
  > 只要一個結構能把「一次演化」寫成整數列，那麼它的守恆律就能被 (i) 自動導出（§9）、
  > (ii) 不可篡改地記錄（§17）、(iii) 隨時稽核與重放（§17.2）—— 三者共用同一份資料。

---

## 18. `relations`：五種關係作為「導出擴展定理」的機制

本節是本輪「導出擴展演算法及定理」的**方法論核心**：所有新命題都必須由五個 lens 之一推出，
而不是直接斷言。`Rec{kind, a, b, holds}` 把每條關係壓成可入賬的整數列（`rec_values`）。

### 18.1 相對（kind 0）：以基準歸一 ⟹ 尺度不變量

* **[D-Rel]** `relative(a,b,p) = a·b⁻¹`（`F_p`）；**[D-RelProfile]** 逐項除上首項。
* **[T-Rel-Scale]** `ys = c·xs ⟹ profile(xs) = profile(ys)`（`c ≠ 0`）。
  `[3,6,9,12] → [1,2,3,4]`（`p = 10007`）、`[1,2,4,8] → [1,2,4]`（`p = 11`）。
  **演算法** `[E-RelProfile]`：任何「量綱」資料先除以基準再比較，於是可以跨尺度對照（這正是 §9 帳本欄位的正規化）。

### 18.2 對偶（kind 1）：轉置、伴隨、置換

| 標籤 | 陳述 | 實測 |
|---|---|---|
| `[T-Dual-Rank]` | `rank A = rank Aᵀ`，且 `nullity(A) − nullity(Aᵀ) = cols − rows` | 隨機 `n×(n+1)`、`p ∈ {7,10007}`、`n = 2..4` 全成立 |
| `[T-Dual-Chain]` | `δ^k = (∂_{k+1})ᵀ`、`∂∂ = 0`、`dim H^k = dim H_k` | `VR(C₄,1)`、`VR(C₅,1)`、`VR(C₆,2)` 皆 `(true, true)`；且 `β(VR(C₄,1)) = (1,1)` 與 §7 一致 |
| `[T-Dual-Radon]` | `rank R = rank Rᵀ = n²` ⟹ Radon 變換單射 | `n = 2,3,5`：`rank = 4/9/25`、`injective = true` |
| `[T-Dual-Tensor]` | `hyperdet222` 在 **6** 個指標置換下不變 | 25 個隨機 `F₃` 張量全成立 |

* **修正（本輪抓到的真錯）**：原稿寫「`nullity(A) = nullity(Aᵀ)`」——對長方形矩陣是**錯**的
  （`n×(n+1)` 時兩者差 1）。正確形式是上面的「指標」等式；第一次跑測試就是被這條擋下來的。
* **算法** `dim H^k` 用**兩條獨立路徑**算（下鏈秩 vs 上鏈轉置秩），不是用同一個數字複製兩次 ——
  否則「對偶」只是恆真句。

### 18.3 對比（kind 2）：差集分割

* **[D-Contrast]** `contrast(a,b) = (只在A, 只在B, 兩者皆是)`（三者皆為布林遮罩）。
* **[T-Contrast-Partition]** 三塊**互斥**且併集恰為 `A ∪ B`：`|onlyA| + |onlyB| + |both| = |A ∪ B|`。
  演算法 `check_contrast_partition` 直接回傳布林（互斥 + 覆蓋）。
* 實測（5 謂詞表，`F₃` 的 6561 個張量）：`rank ≤ 1` 對 `Det = 0` 給出 `onlyA/onlyB/both = 0/2112/129`
  ⟹ `rank ≤ 1` 的 129 個張量**全部**滿足 `Det = 0`（`onlyA = 0` 即是蘊含的數值證據）。

### 18.4 蘊含（kind 3）：有限樣本上的蘊含格

* **[D-Implies]** `p ⟹ q` ⟺ 不存在「`p` 真而 `q` 假」的樣本；**[E-ImplClosure]** Floyd–Warshall 傳遞閉包；
  **[T-Impl-Equiv]** 雙向蘊含 = 等價。
* **[T-Impl-Matrix]** 對 `F₃` 全部 6561 個 `2×2×2` 張量、5 個謂詞
  （`0: rank ≤ 1`、`1: Det = 0`、`2: rank-2 分解數 = 0`、`3: rank = 3`、`4: Det ≠ 0`），蘊含矩陣為

  ```
       0 1 2 3 4
  0    1 1 1 0 0      rank ≤ 1  ⟹  Det = 0, rank2 分解數 = 0
  1    0 1 0 0 0      Det = 0  ⇏  rank ≤ 1（反例：秩 2 的 Det = 0 張量）
  2    0 0 1 0 0
  3    0 0 1 1 0      rank = 3  ⟹  rank2 分解數 = 0
  4    0 0 0 0 1      Det ≠ 0   ⇏  rank = 3（§11 的負面結果 (1)）
  ```

* **結果**：閉包 = 原矩陣（已傳遞），**等價類 = 0 個**。
  ⟹ 原猜想「`rank ≤ 1 ⟺ Det = 0 ⟺ #decomp = 0` 是一個等價類」**被計算否決**：
  真實結構是**三條單向蘊含** + 兩條反例。這正是「蘊含 lens」的價值 —— 它把「聽起來對」的等價關係
  壓成「單向」，並給出反例存在的方向。
* 算法 `[E-ImplMatrix]` 的成本 = `5² × 6561` 次謂詞查詢；換任何一族有限結構都可重跑。

### 18.5 比率（kind 4）：與尺度無關的常數

| 標籤 | 陳述 | 實測 |
|---|---|---|
| `[D-Ratio]` | 約分後的比值（分母 0 → `(0,1)`） | — |
| `[E-ConstantRatio]` | 一族比值全等時回傳該值，否則 `None`（**不硬給值**） | `[(1,2),(1,3)] → None` |
| `[T-Ratio-Radon]` | `Σ_lines(Rf) : Σ_x f = (n+1) : 1` | `n = 2,3,5`、多個 `f` 皆得 `n+1`（`n=3` 即 `4:1`） |
| `[T-Ratio-Flip]` | 翻轉圖 `k`-正則 ⟹ `E : V = k : 2 = (n−3) : 2` | `n = 5,6,7` → `1:1`、`3:2`、`2:1` |

* **前提必須寫進命題**：`Σ f ≡ 0` 時 `Σ(Rf)/Σf` **不存在**（回傳 `None`）。測試特別造了一個零均值 `f`
  來確認「不會給出比值」—— 這是把「定理的必要條件」變成程式的一部分。

### 18.6 收集與入賬

* **[E-Collect]** `collect(n_radon, p)` 把五類 lens 的代表性計算收成 `Rec` 列；`rec_values` 壓成 `(kind, a, b, holds)`。
* **[E-CollectInto]** `collect_into_ledger(l, n, p)` 把每一條關係寫進 §17 的持久賬本
  （`kind = 2` 宣稱），可 `verify`、可 `fork_index`、可 `replay`。實測 `moon run cmd/main`：
  `collect(2,10007)` → 4 條全 `holds`；入賬後鏈長 `8 → 12`、`verify = true`。

### 18.7 由五個 lens 導出的「擴展定理與算法」清單

| # | 由哪個 lens | 新定理／算法 | 型態 |
|---|---|---|---|
| 1 | 相對 | `[T-Rel-Scale]` 剖面尺度不變；`[E-RelProfile]` | 恆等式（演算法：歸一化） |
| 2 | 對偶 | `[T-Dual-Rank]` 指標等式（**修正**原稿錯誤） | 不等式 + 等式 |
| 3 | 對偶 | `[T-Dual-Chain]` `dim H^k = dim H_k`（兩條獨立路徑） | 等式 |
| 4 | 對偶 | `[T-Dual-Radon]` `rank R = n²` ⟹ 單射 | 等式 ⟹ 命題 |
| 5 | 對偶 | `[T-Dual-Tensor]` 超行列式對 6 個指標置換不變 | 不變量 |
| 6 | 對比 | `[T-Contrast-Partition]` 三塊互斥且覆蓋 `A ∪ B` | 分割恆等式 |
| 7 | 蘊含 | `[T-Impl-Matrix]` 蘊含格（3 條單向 + 2 條反例，等價類 0） | 結構定理 + 反例 |
| 8 | 比率 | `[T-Ratio-Radon]` `Σ(Rf):Σf = (n+1):1`（零均值時不存在） | 常數比 + 前置條件 |
| 9 | 比率 | `[T-Ratio-Flip]` `E:V = (n−3):2` | 常數比 |
| 10 | 五者合用 | `[E-Collect]/[E-CollectInto]`：關係 → 整數列 → 賬本 → 稽核 | 演算法（可重跑） |
| 11 | 五者合用 | 跨層命題：導出（§9）+ 記錄（§17）+ 稽核（§17.2）+ 對偶/蘊含（§18） | 方法論命題 |

---

## 19. 譜序列引擎（`ss`）：把「一頁」變成可運算的物件

### 19.1 定義

* **[D-Page]** 一頁 `Page { r, p0, q0, np, nq, dims, d, p, qflip }`：
  `dims[i][j]` 是 `E_r^{p0+i, q0+j}` 的維數，`d[i][j] : E_r^{p,q} → E_r^{p+r, q−r+1}` 是一個矩陣
  （`None` 表示零映射）。`qflip = true` 時改用另一種雙次約定 `(p+r, q+r−1)`（Adams 型）。
* **[E-DQ]** `page_dq` = `r−1`（qflip）或 `−(r−1)`（標準）；`page_target_q` / `page_source_q` 由它導出。

### 19.2 定理

| 標籤 | 陳述 | 驗證 |
|---|---|---|
| `[T-SS-DD]` | `d_r ∘ d_r = 0` 逐格成立（矩陣乘法） | `page_dd_zero`：Hopff、T³、Adams 頁皆 true |
| `[E-PageNext]` | `E_{r+1}^{p,q} = ker d_r / im d_r` | `page_hom_dim = ker_dim − im_dim` |
| `[T-SS-Kill]` | 1×1 的非零 `d_r` 同時消掉源與靶兩格 | 5/5 測試中「a 1x1 differential kills both cells」 |
| `[T-SS-Total]` | 取下一頁不改變分次總維數（`Σ_{p+q=n}`） | `totals are preserved by page_next` |

* **關鍵實作事實**：標準約定下 `d_r` 的雙次是 `(r, 1−r)`（源 `(0,j)` → 靶 `(2, j−1)`），
  這個「1−r」的 q 位移是 §21、§24 全部計算的正確性前提；寫錯會讓 `d_r` 落到視窗之外而不報錯。
* **[T-SS-Flip]** `qflip = true` 時 `page_target_q(page, 1) = 2`（r=2），`page_source_q(page, 2) = 1`。

---

## 20. 塞爾譜序列（`serre`）與交叉驗證

* **[E-SerreE2]** `serre_e2(bb, bf, p)`：以底空間維數 `bb`、纖維維數 `bf` 建 `E_2^{p,q} = H^p(B) ⊗ H^q(F)`。
* **[T-Serre-Conv]** `E_∞` 的總維數 = 底空間獨立算出的 Betti 數 ⟹ 收斂（`fit ∧ exact`）。

| 例子 | 結果 |
|---|---|
| Hopf `S¹ → S³ → S²`（p=7） | `E_2` 4 格；`d_2 ≠ 0` ⟹ `E_3` 總維數 `[1,0,0,1]` = `cx_betti_all(S³)`；`serre_sphere_converges(1,1,7) = true` |
| 球叢 `S^n → S^{2n+1} → S^{n+1}`，`e = 1,2`（mod 11） | `n = 1,2,3` 全部收斂；`e = 0` 時 `page_zero_diffs = true` |
| `S² × S³` | `cx_betti_all = [1,0,1,1,0,1]`；退化兩列 ⟹ `page_converges = (true, true)`（**無擴張問題**） |
| 扭曲係數 | `V = F_2, g = −1` → `(invariants, coinvariants) = (1,1)`；`F_7` 上 `(0,0)`；`diag(1,−1)` on `F_7²` → `(1,1)` |

* **[E-SerreCross]** `serre_matches_homology(page, cx)`：把 `E_∞` 與 `@cellcx.cx_betti_all` 直接比對，
  是「兩條獨立演算法互相稽核」的實作（不是同一條路徑算兩次）。

---

## 21. Adams 譜序列（`adams`）：Ext_A(F₂,F₂) 的最小自由分解

### 21.1 演算法

* **[E-Adem]** `adem(i, j)` 產生 Adem 關係的項；`mono_mul` 用它把 `Sq^I · Sq^J` 化成可容許基的線性和。
* **[E-MinRes]** `ext_table(al, s_max, t_max)`：`F_0 = A`，`K_s = ker(F_s → K_{s−1})`，
  `Ext^{s,t} = dim (K_s / A⁺K_s)_t`，其中 `A⁺K_s` 的生成元逐一由 `al.tab[ai]` 作用在 `K_s` 的基上，
  再以**行階梯消去**（`f2_echelon` / `f2_reduce_vec`）取商。
* **[T-Trunc]** 截斷不改變低度數的 Ext：`D = 8` 與 `D = 6` 在 `t ≤ 6` 上逐項相等。

### 21.2 算出來的表（p = 2，`D = 8`，`s ≤ 3`、`t ≤ 8`）

```
        t=0 1 2 3 4 5 6 7 8
 s=0     1 0 0 0 0 0 0 0 0
 s=1     0 1 1 0 1 0 0 0 1     ← 不可分解元：deg 1, 2, 4, 8
 s=2     0 0 1 0 1 1 0 0 1     ← h₀²(2,2)、h₁²(2,4)、h₀h₂(2,5)、?(2,8)
 s=3     0 0 0 1 0 0 1 0 0     ← h₀³(3,3)、c₀(3,6)
```

* **重要校正（相對於「猜想值」）**：`Ext^{2,3} = 0` 而不是 1。原因是 `h₀·h₁ = 0` 在 `Ext_A` 中成立
  （Beaudry–Campbell 的導引與 arXiv:2105.02601 的 `E_2(ko)` 關係都寫明 `h₀h₁ = 0`）。
  這條不是猜的：引擎在 `(s,t) = (2,3)` 真的算出 0。
* `Ext^{s,s} = 1`（`h₀`-塔）、`Ext^{s,t} = 0`（`t < s`）如預期。
* **[T-Trunc]** 截斷不改變低度數：`D = 6` 與 `D = 8` 在 `t ≤ 6` 逐項相等（測試 `truncation stability of Ext`）。
  **邊界聲明**：`t = 8` 那一欄是截斷代數的 Ext，可能含截斷造成的偽類；本檔不聲稱它是 `Ext_A` 的全部。
### 21.3 對照組（演算法正確性的獨立證據）

* **[T-Koszul]** 取 `A = E(Sq¹) = F₂[Sq¹]/(Sq¹²)`（外代數），則 `Ext_A(F₂,F₂) = F₂[h₀]`：
  引擎算出「每個 `(s,s)` 恰好一維、其餘為零」，與 Koszul 對偶的已知答案一致。
  這證明最小自由分解引擎本身正確，故 §21.2 的 `Ext^{2,3} = 0` 是 `A` 的真實性質，而不是程式錯誤。

### 21.4 接到譜序列

* **[E-AdamsPage]** `adams_page(ext, p)` 把 Ext 表放進 `@ss.Page`（`qflip = true`，`r = 2`）；
  `adams_stem_dims` 讀出莖 `t − s` 上的 E₂ 維數：莖 0 = 4（`1, h₀, h₀², h₀³`）、莖 1 = 1（`h₁`）。

---

## 22. 格羅滕迪克拓撲（`grotop`）

### 22.1 定義與演算法

* **[D-Site]** 有限偏序集 `(n, leq, p)`；**[D-Sieve]** sieve = 向下封閉的開集集合（布林陣列）；
* **[D-Meet]** `site_meet`（最大下界，不存在回 `−1`）；
* **[E-Saturate]** `top_of_families`：由覆蓋族生成拓撲 —— 加入最大 sieve、對所有 `V ⊆ U` 取拉回、直到封閉。
* **[D-Topology]** 拓撲同時保存「已飽和的 sieve 族」`cov`（供公理檢查）與「登錄的覆蓋族」`fams`（供層條件檢查）。

### 22.2 公理是機器驗證的

| 標籤 | 公理 | 實作 |
|---|---|---|
| `[T-Top1]` | (T1) 最大 sieve 覆蓋 | `top_axiom_max` |
| `[T-Top2]` | (T2) 拉回穩定 | `top_axiom_pull` |
| `[T-Top3]` | (T3) 局部刻劃 | `top_axiom_local` |

* **正例**：離散拓撲、混沌拓撲、由 `{A,B} 覆蓋 U` 生成的拓撲全部通過（`top_valid = true`）。
* **反例（測試真的抓到）**：拿掉最大 sieve ⟹ (T1) 失敗；只宣告 `{A}` 覆蓋 `U` 而不宣告拉回 ⟹
  `f*S = {∅}` 在 `B` 上不是最大 sieve ⟹ (T2) 失敗。

### 22.3 層條件

* **[T-Sheaf]** 對覆蓋族 `(U_i)` 檢查正合性
  `0 → F(U) → ∏ F(U_i) → ∏ F(U_i ∧ U_j)`，Čech 微分 `(d¹σ)_{ij} = σ_j − σ_i`
  （`i = j` 的塊自動為零 ⟹ `d¹d⁰ = 0`，這是實作正確性的內部檢核）。
  回傳 `(injective?, exact?, dim ker d⁰, dim ker d¹, rank d⁰)`。
* **常數預層不是層**（`1 ≠ 2`）；**「點上的函數」層是層**（`k⁰ = 0, k¹ = r⁰ = 2`）。
* **[E-Plus]** 加號構造的維數 = 相容族維數；對覆蓋族取**最大值**（colimit 的單調性，不是最小值）。

---

## 23. 凝聚集／凝聚群（`condensed`）

以「有限層級鏈」表示凝聚對象：`S = lim_n S_n`（`sizes`, `maps`），映射是 one-hot 矩陣。

| 標籤 | 陳述 | 演算法 |
|---|---|---|
| `[T-Prof]` | 合法 profinite 呈現：每欄恰一個 1、每列至少一個 1 | `prof_valid` |
| `[E-Free]` | `Z[S]^■` 的層級鏈 = `Z[S_n]` 與誘導映射 | `chain_free` |
| `[E-Func]` | 函數鏈 `C(S_n, F_p^k)`（正向系、單射） | `chain_func` |
| `[E-Lim]` | 逆極限維數 = 複合映射的秩 | `chain_lim_dim` |
| `[T-ExtVan]` | 自由鏈到上 + 函數鏈單射 ⟹ Mittag-Leffler ⟹ `Ext^{i>0}(Z[S]^■, F_p) = 0` | `cond_ext_vanishes` |
| `[T-Tensor]` | `Z[S]^■ ⊗ Z[T]^■ ≅ Z[S × T]^■` | `chain_tensor` vs `chain_free(prof_prod)`，**逐層矩陣相等** |

### 23.1 固態性：一個真正算得出來的缺口

* **[T-Solid]** 對離散目標 `A = F_p^k`：
  `Hom(Z[S], A) = lim_n C(S_n, A) = C(S_0, A)`（只有「常數型」），
  `Hom(Z[S]^■, A) = colim_n C(S_n, A) = C(S_N, A)`（全部局部常數），
  缺口 `= k(|S_N| − |S_0|) > 0` ⟹ **`F_p` 不是固態群**。
  實測 `Z_2`（層級 2,4,8）：`2 → 8`，缺口 6；三維係數 `6 → 24`；單點缺口 0。
* **[T-SolidCompact]** 對緊目標 `Z_p`（`= lim Z/p^n`）：兩邊都是 `lim_n (Z/p^n)^{|S_0|}`，
  **缺口恆為 0** ⟹ `Z_p` 固態。這兩條把「固態」從形容词變成可計算的判準。

> **邊界聲明**：本引擎只覆蓋 profinite（有限層級）情形。`Ext^{i>0}` 的非零只能出現在
> 非 profinite（「輕凝聚」`N∞` 型的無窮維係數）情形；本檔對 `N∞` 只驗證了 ML 證書，未聲稱計算非零 Ext。

---

## 24. 扭曲 AHSS（`ahss`）

### 24.1 模型

* **[D-Alg]** `H^*(X;F_p)` 是顯式分次代數：`dims` + 乘法表 `cup[i][j]`（列 = `H^{i+j}`、欄 = `a·dims[j] + b`）。
* **[D-Wedge]** `alg_wedge(degs)`：外代數（球面、環面、`S²×S³` 全部涵蓋）；
  **[D-Tensor]** `alg_tensor`：`H^k(A⊗B) = ⊕_{i+j=k} H^i(A) ⊗ H^j(B)`。
* **[T-Assoc] / [T-Unit]** 結合律與單位元用**克羅內克積 + 矩陣相等**機器驗證
  （`(xy)z = x(yz)` 對所有基三元組）。

### 24.2 微分

* **[E-CupOp]** `cup_operator(a, 3, h)` 建出 `H∪(−)` 的矩陣族。
* **[T-Sq3]** `dim X ≤ 5` ⟹ `Sq³ = 0`：`deg x ≤ 2` 由不穩定性 `Sq^i x = 0 (i > |x|)`；
  `deg x ≥ 3` 時 `Sq³x ∈ H^{≥6} = 0`。這是**推導**出來的，不是假設的零算子。
* **[E-AhssD3]** `d_3 = Sq³ + H∪(−)`，雙次 `(3, −2)`（引擎標準約定）。

### 24.3 計算結果

| 例子 | 結果 |
|---|---|
| `S³`，`H = 0` | `page_zero_diffs = true`；`E_2 = E_∞`，`page_total(·,0) = 1` |
| `S³`，`H = x`（`H³` 生成元） | `d_3(1) = x`；`E_4` 的源（`H⁰`）與靶（`H³`）同時被殺 ⟹ 三層塔總維數 `0` |
| `T³`，`H = xyz` | `page_dd_zero = true`；`E_4`：`H⁰` 被殺、`H¹ = 3`、`H² = 3` 不動、`H³` 被殺 |
| `S²`，任何 `H` | `H³ = 0` ⟹ twist 不可見（`ops_is_zero = true`） |

---

## 25. 交叉運算（`xops`）：四者互動導出的新定理

> 這一節的每條定理都**同時用到至少兩個套件**，不是任何單一套件的重述。

| 標籤 | 陳述（由哪些結構交互而來） | 驗證 |
|---|---|---|
| `[T-X-Vanish]` | **扭曲 K × AHSS**：`H³(X;Z) = 0 ⟹ d_3 = Sq³`，且 `dim X ≤ 5` 時 `Sq³ = 0`，故 twist 完全不可見。 | `S², S¹` → 不可見；`S³, T³, S²×S³` → 可見 |
| `[T-X-Sum]` | **扭曲 AHSS × 拓撲分解**：`E_∞` 對不相交並可加。把 `alg_sum` 的塊對角乘法 + 只在一份上生效的 twist 一起算，得 `Σ_n E_∞(X⊔Y) = Σ_n E_∞(X) + Σ_n E_∞(Y)` 逐分次成立。 | 5 個分次全 true |
| `[T-X-Site]` | **非交叉樹 × 格羅滕迪克拓撲**：非交叉森林（位元遮罩、`@nc.chords_cross` 判交叉）的「分量覆蓋」是一個格羅滕迪克拓撲。(T1)(T2)(T3) 在 `n = 3` 全驗；`n = 4` 驗 (T1)(T2)（(T3) 成本過高，如實聲明）。 | `n=3`: 8 個開集全通過；`n=4`: 48 個開集（64 − 16 個含交叉對的遮罩） |
| `[T-X-Obstruct]` | **格羅滕迪克拓撲 × 扭曲 AHSS**：局部給定的 twist 類要黏成整體類的障礙 `= Σ(k¹ − r⁰)`。可黏（常數層、弦上函數層）→ 0；限制映射為零的「假 twist」→ 正。 | `good → 0`、`bad > 0`、`F_p^{|U|} → 0` |

* **[T-X-Obstruct] 的意義**：`H³` 是扭曲 K 理論的唯一入口（§24），而「`H³` 是否為整體類」
  正是它在格羅滕迪克拓撲上的層條件；因此 `k¹ − r⁰` 是一個**可計算的扭曲存在性判準**：
  它把「有一個 twist 類」與「有一族局部 twist 類」區分開來。
* 三條測試同時也是**反例檢核**：`bad` 的 `is_sheaf = false` 與 `obstruction > 0` 必須同時成立，
  否則就是實作把「局部」誤當「整體」。

---

## 26. 重跑總表（第三輪）

```sh
export PATH="$HOME/.moon/bin:$PATH"
cd tensorlab
moon check          # 0 errors, 0 warnings
moon test           # Total tests: 163, passed: 163, failed: 0
moon run cmd/main   # 171 行報告（§19–§25 + §28 規範形）
```

| 套件 | 測試數 | 主題 |
|---|---|---|
| core / tensor / nc / twist / radon / gauge / metric / evolve | 10 / 12 / 10 / 8 / 5 / 9 / 6 / 7 | §1–§9 |
| hyper / spectral / ledger / relations | 7 / 12 / 7 / 8 | §13–§18 |
| **cellcx** | 3 | CW 複形、透鏡空間撓率、持續條碼 |
| **ss** | 5 | 譜序列引擎（雙次、消滅、張量、qflip） |
| **serre** | 4 | 塞爾譜序列與胞腔同調交叉驗證 |
| **adams** | 5 | Adem 關係、Ext 表、Koszul 對照、Adams 頁 |
| **grotop** | 6 | site/sieve/覆蓋公理/層條件/加號構造 |
| **condensed** | 5 | profinite 鏈、Ext 消失、固態缺口、張量同構 |
| **ahss** | 6 | 分次代數、Sq³ 消失、扭曲 d₃、E₄ 計算 |
| **dtensor** | 4 | 導出張量積：Koszul 分解、Tor = C(2g,i)、Künneth |
| **xops** | 5 | 四結構交互定理 + Koszul 對偶（Ext vs Tor） |
| **canon** | 19 | 逐結構規範形（完備性、冪等性、不變性） |

---

## 27. 導出張量積（`dtensor`）：Tor 用兩份自由分解真算

### 27.1 為什麼不能只用一份分解

* **[T-Tor-Right]** `Tor_*^A(F_2,F_2) = H_*(K_* ⊗_A K'_*)`：必須**同時**用兩份自由分解
  （`F_2 ⊗^L_A F_2` 的定義），不能只用一份 `K_*`。
  用一份分解算出的數其實是 `Ext` 那一側的答案 —— 這個「差一側」的錯誤在實作過程中真的發生過
  （見 CODE_HEALTH §6.1 #10），修法就是改成 `K ⊗_A K'`。

### 27.2 演算法

* **[D-Poly]** `A = F_2[x_1..x_g]`（生成元度數 1，截斷到總度數 `n`）。
* **[D-Koszul]** `K_i = ⊕_{|S|=i} A·e_S`，`d_i(e_S·m) = Σ_{j∈S} (S∖j, m+e_j)`（F_2 無號）。
  基的內部度數 = `i + |m|`，矩陣由 `koszul_d` 逐項建出。
* **[T-KoszulDD]** `d² = 0`：對 `g = 1,2,3` 的每個內部度數格子用矩陣乘法驗證。
* **[T-KoszulExact]** `K_*` 確是 `F_2` 的自由分解：`dim ker d_i = rank d_{i+1}` 逐格成立。
* **[E-Tor]** 約化複形 `K ⊗_A K' ⊗_A F_2`：基 = 兩份子集對 `(S_1,S_2)`，同調度 = `|S_1|+|S_2|`；
  微分矩陣由「取常數項」逐項計算（本模型中係數全在 `A⁺`，故矩陣為零 —— 但這是**算出來的**）。
  `Tor_i = dim ker(d_i⊗1) − rank(d_{i+1}⊗1)`。

### 27.3 結果

| 代數 | 計算結果 |
|---|---|
| `A = F_2[x]` | `Tor_0, Tor_1, Tor_2 = 1, 2, 1`（= `Λ(u₁,u₂)`），`Tor_{i≥3} = 0` |
| `A = F_2[x,y]` | `1, 4, 6, 4, 1`（= `Λ` on `2g = 4` 個生成元） |
| `A = F_2[x,y,z]` | `Tor_1 = 6`、`Tor_3 = 20`、`Tor_6 = 1` |
| **Künneth** | `Tor^{A⊗B}_i = ⊕_{i₁+i₂=i} Tor^A_{i₁} ⊗ Tor^B_{i₂}`（三張表獨立算出，逐格相等） |

* **[T-X-Koszul]（§25 追加）** Koszul 對偶的兩面：`Ext_{Λ(V)}(F_2,F_2)` 在 `(i,i)` 恆為 **1**（`@adams`），
  而 `Tor^{Sym(V)}_i(F_2,F_2)` 為 **C(2g,i)**（`@dtensor`）。兩個引擎、兩條路徑、互為見證。

---

## 28. 逐結構規範形化（`canon`）

### 28.1 什麼叫「一個結構的規範形」

對每個結構給三件事：

* **(C1) 可計算的 canon**：一個函式 `canon(x)`，輸出可直接比較的整數鍵。
* **(C2) 完備性**：`canon(x) = canon(y) ⟺ x ~ y`，其中 `~` 是**明寫出來的**等價關係
  （列等價、么模等價、同格、相似、同構、等距、腿置換、二面體、上同調、規範、同倫…）。
* **(C3) 不變性**：在 `~` 下不變；測試用**真正的重標號／共軛／換基**驗證，不是口頭聲明。

兩條全域公理（每條測試都在驗）：
`[Ax-Canon-Idem]` `canon(canon(x)) = canon(x)`；
`[Ax-Canon-Complete]` 見 (C2) —— **不完備者一律如實標註，不假裝完備**。

### 28.2 十九個結構的規範形總表

| # | 結構 / 套件 | 規範形（演算法） | 等價關係 | 完備？ | 驗證方式 |
|---|---|---|---|---|---|
| 1 | 矩陣 over F_p（core） | **RREF**（`canon_rref`） | 列等價（同一列空間） | ✅ | `M_{2×3}(F₂)` 全 64 個矩陣 ⟹ 恰 **15** 類 = F₂³ 的子空間數 |
| 2 | 整數矩陣（core） | **Smith 對角線**（`canon_snf`） | 么模等價 | ✅ | `diag(2,3) ~ diag(1,6)`、整除鏈 |
| 3 | 整數**格**（core） | **Hermite 正規形**（`canon_hnf`） | 生成同一個格 | ✅ | 不同生成集同 canon；單列 `[6,9]` 的正規形就是它自己 |
| 4 | 線性映射（spectral） | **共軛軌道最小元**（`canon_conj`，窮舉 GL_n） | 相似 | ✅ | `M₂(F_q)` 類數 = **q²+q**（`q=2→6`、`q=3→12`）；Σ類大小 = 16 |
| 5 | 圖（spectral, metric） | **S_n 軌道最小元**（`canon_graph`） | 同構 | ✅（n ≤ 7） | P₄ ≠ K_{1,3}；旋轉標號同 canon |
| 6 | 有限度量空間（metric） | 同上作用於距離矩陣（`canon_metric`） | 等距 | ✅ | 重標號不變；直線 vs 星形不同 |
| 7 | 3-張量（tensor） | **腿置換 S₃ 最小元**（`canon_t3`） | S₃ 腿置換 | ✅（對 S₃） | 2×2×2 的 256 個張量：**canon 軌道數 = Burnside 值** |
| 8 | 非交叉結構（nc） | **二面體 D_n 最小元**（`canon_dihedral`） | D_n 等價 | ✅ | 5 邊形族：軌道數 = Burnside 值；邊 ≠ 對角線 |
| 9 | 2-上圈（twist） | **上同調類中字典序最小者**（`canon_cocycle`） | ω ~ ω+δ¹f | ✅ | `(Z/2)², ℓ=2`：相異 canon 個數 = `|H²| = 2³ = 8` |
| 10 | 格點規範場（gauge） | **曲率場**（`canon_gauge`） | 規範變換 | ⚠️ **不完備** | 曲率不變（真驗）；環面上「平坦但 holonomy≠0」與零場同曲率卻不同軌道 |
| 11 | 超結構（hyper） | 成員表（`canon_hyper`）／S_n 最小元（`canon_hyper_iso`） | 逐項相等／同構 | ✅／✅ | Z/4 ≠ V₄；非自同構置換造的同構副本 canon 相同 |
| 12 | 關係記錄（relations） | **排序去重**（`canon_records`） | 集合相等 | ✅ | 次序與重複不影響 |
| 13 | CW 複形（cellcx） | **每個邊界的 Smith 對角線**（`canon_cx`） | 逐度么模等價 | ⚠️ 不完備於同倫等價 | 換基（乘 −1）不變；S² ≠ L(5,1) ≠ L(7,1) |
| 14 | 譜序列頁（ss, serre, adams） | `(r, dims, 每個 d_r 的 RREF)`（`canon_page`） | 逐格換基 | ✅ | `d ↦ Q d P⁻¹` 後 canon 不變 |
| 15 | 分次代數（ahss） | **秩剖面** `dims + rank(cup[i][j])`（`canon_alg_profile`） | 逐度基變換 | ⚠️ 不變量，不完備 | `P_{i+j} C (P_i ⊗ P_j)` 後剖面不變 |
| 16 | 凝聚鏈（condensed） | `dims + 每個過渡的 Smith`（`canon_chain`） | 逐層么模等價 | ⚠️ 不完備於鏈同構 | 換基不變；逆極限維數由它決定 |
| 17 | 導出張量積（dtensor） | **Tor 雙次表**（`canon_tor`） | 表相等 | ✅ | 截斷 4 與 6 在低度數一致 |
| 18 | site / 拓撲（grotop） | 偏序矩陣的 **S_n 最小元**（`canon_poset`） | 偏序同構 | ✅（n ≤ 7） | 換標號不變；鏈 ≠ V 形 |
| 19 | 帳本（ledger） | 雜湊鏈 tip（既有 `ledger_tip`） | 逐項相同 | ✅（雜湊碰撞除外） | 篡改偵測（§17） |

### 28.3 細化階梯（`[T-Canon-Ladder]`）

同一批物件上有粗細不同的規範形，本檔逐條證明它們的**嚴格細化**關係：

```
canon_graph  ≻  canon_conj  ≻  char poly          （圖同構 ⟹ 相似 ⟹ 同特徵多項式）
canon_cx     ≻  (Betti, 撓率)                     （Smith 資料決定同調，反之不成立）
canon_snf    ≻  rank
canon_page   ≻  dims
canon_hnf    ≻  rank
```

* **`canon_conj ≻ char poly` 的嚴格性是算出來的**：`diag(1,1)` 與 `[[1,1],[0,1]]` 在 F₃ 上同特徵多項式
  `(x−1)²`，但極小多項式不同 ⟹ `canon_conj` 不同。
* **`canon_graph ≻ canon_conj`**：換標號是**置換**相似，置換 ⊂ GL，故 graph canon 相同蘊含 conj canon 相同；
  在 3 個頂點的全部 8 張圖上逐對驗證了這個蘊含。

### 28.4 這一節得到的**方法論**結論（比定理更有用）

1. **定理要求的「前提」必須寫進測試，否則測試會假失敗**。二面體 Burnside 測試第一次給出
   `軌道數 4 ≠ Burnside 3`：不是 Burnside 錯，而是我選的邊集族在 D₅ 下**不封閉**（Burnside 只對
   G-不變的族有效）。修正族之後兩者一致。
2. **用自同構做「重標號測試」會假通過**。對交換群 Z/4 用自同構 σ 重標號，乘法表**逐項不變**，
   於是「同構但編碼不同」的斷言自動成立。改用**非自同構**置換後才真正測到東西。
3. **不完備的規範形也要寫出來，並附見證**。曲率對環面規範場不完備：平坦但 holonomy≠0 的場
   與零場同曲率、不同軌道（窮舉 `(Z/2)^9` 的 512 個規範變換確認零場軌道只有零場）。
4. **規範形的代價是群作用窮舉**：`canon_conj` 是 `|GL_n(F_p)|`、`canon_graph` 是 `n!`，
   所以每個函式都標明可算範圍（`n ≤ 3, p ≤ 3` / `n ≤ 7`），而不是假裝普遍可用。
