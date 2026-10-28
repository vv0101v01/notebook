# SUPER_THEORY —— tensorlab 的超化（ℤ₂ 分次）與譜化擴充理論

本文件記錄「superlab」擴充的數學內容：對原 7 結構（core/tensor/nc/twist/gauge/
radon/metric/evolve）逐一施行

1. **超化**：ℤ₂ 分次（奇偶）、Koszul 號（−1)^{|a||b|}、分次交換子／超跡／
   Berezinian——「展平對稱性」：把交換中的對稱換成反交換中的對稱；
2. **譜化**：特徵多項式、Jacobi 特徵值、譜流、Witten 指標、flip 圖譜、
   Radon 奇異譜、VR 條碼、Betti 譜、Hodge 分解；
3. **認識論標記**：每個敘述帶 `[S-Ax/D/P/T/C/E/Inv/S-NEG-]` 標籤
   （定義／算法／定理／計算驗證／擴充定理／不變量／否定性結果）。

所有命題皆有對應 MoonBit 測試（`moon test`，125 項全綠）。

---

## 0. 標記體系

| 標籤 | 意義 | 認識論地位 |
|---|---|---|
| `[S-Ax]` | 分次公理（ℤ₂、Koszul 號） | 約定＋可驗證的相容性 |
| `[S-D]` | 定義／算法（可執行） | 由測試釘死正確性 |
| `[S-T]` | 定理（有證明、並被計算驗證） | 雙重確認 |
| `[S-C]` | 計算發現（先由計算觀察、後補論證） | 本實驗室原產 |
| `[S-NEG]` | **否定性結果**：某命題被計算否決 | 反例俱在 |
| `[S-GENESIS]` | 帳本創世 | 持久性錨點 |

---

## 1. score —— 超矩陣代數

**分次環** `Λ_k = F_p[θ₁..θ_k]/(θᵢθⱼ = −θⱼθᵢ)`（ bitmask 表示；
`gr_mul` 帶 Koszul 號）。

* `[S-T-strCyc]` **分次跡循環性**：str(MN) = str(NM) 對 Λ 上的矩陣**總是**成立；
  對純 F_p 上的分齊次偶矩陣 X（任意 Y）成立。
* `[S-NEG-strPlain]` **反例**：str(MN) = str(NM) 在純 F_p、非齊次矩陣上**失敗**
  （測試中以構造的 b/c 塊矩陣否決）。
* `[S-T-FlatSym]` **展平對稱性**：Sym^d(V₀)⊗Λ^•(V₁) 的維數
  Σⱼ C(n_odd, j)·C(n_even + d − j − 1, d − j)。
* `[S-T-Ber]` **Berezinian** sdet 的乘法性、對角情形、ε-展開
  Ber(I + εs) = 1 + ε·str(s)；`[S-NEG-BerField]` 純體上不存在非平凡
  Berezinian（b = c = 0 ⟹ 平凡）。
* `[S-D-Gr]` Grassmann 引擎：θ² = 0、反交換、結合、偶元素交換、可逆性。

## 2. spec —— 譜機制

* `[S-D-charpoly]` Faddeev–LeVerrier／**Newton 恆等式**實作（mod p 精確）；
  Cayley–Hamilton 以矩陣代入驗證；`[S-D-jacobi]` 對稱矩陣 Jacobi
  特徵值算法（殘差 < 10⁻⁷、正交性、排序）。
* `[S-T-PowTrace]` tr((AB)^k) = tr((BA)^k)。
* `[S-T-ChPolyRel]` det(xI_n − DDᵀ) = x^{n−m}·det(xI_m − DᵀD)。
* `[S-T-Witten]` 有限維線性 SUSY 的 Witten 指標 = m − n；核維數跳變相消。
* `[S-T-FlowMorse]` **譜流 = Morse 指標變化** flow = n₋(H₀) − n₋(H₁)
  （排序特徵值曲線連續；死區符號追蹤處理精確落在 0 的樣本）。
* `[S-NEG-FlowDet]` **否定性結果**：「flow = ½(sgn det H₁ − sgn det H₀)」
  **被計算否決**——行列式符號只看流的**奇偶**（與 sgn det₀ 的乘性），
  不是流本身。反例：H₀ = diag(−25,−4,20)、H₁ = diag(−26,9,13)：
  flow = +1 但 ½(−1−1) = −1。

## 3. stensor —— 超張量

* `[S-C-KronRank]` 分次（Koszul 扭曲）Kronecker 積 = (A⊗B)·D
  （D = ±1 對角）⟹ rank(A⊗̂B) = rank A · rank B。
* `[S-C-KoszulFlat]` 帶 Koszul 號的展平不改秩（= 右乘可逆對角矩陣）。
* `[S-T-OddAlg]` **奇導子代數**（OSL(1|1)³ 在 8 個座標 T_{ijk} 上）：
  D² = 0、**{D_E, D_F} = 完整 Euler**（每個生成子上都是恆等）。
* `[S-NEG-SDet]` **超四次不變量 = 常數**：6 個奇導子的公共核在四次齊次
  部分為 {0}（由 {D_E,D_F} = 4·Euler：核中元素 4f = 0 ⟹ f = 0 mod 101）。
  ⟹ 不存在超行列式型的 OSL(1|1)³ 四次不變量——純量中心方向的阻礙。
  對照：單一超荷 D_E 的核非平凡（**超對稱破缺**門檻）。

## 4. snc —— 非交換／自由機率的超化

* `[S-D-NCPart]` |NC(n)| = Catalan(n)（n ≤ 7 枚 舉）。
* `[S-T-MobiusNC]` **Kreweras 超積公式** μ(0̂,π) = ∏_B (−1)^{|B|−1}C_{|B|−1}
  對 NC(6) 全部 132 個 π 逐一驗證——Möbius 函數 = 格的「超維數」
  （鏈上的交錯和，ℤ₂ 分次 Euler 特徵）。
* `[S-D-FreeCum]` m_n = Σ_{π∈NC(n)} ∏_B r_{|B|}：r≡1 ⟹ Marchenko–Pastur
  （m_n = Cat n）；r = e₂ ⟹ 半圓律 m_{2k} = C_k、奇矩 = 0。
* `[S-D-vonSzily]` 超卡特蘭 S(m,n) = (2m)!(2n)!/(m!n!(m+n)!) =
  Σ_k (−1)^k C(2m,m+k)C(2n,n−k)（**von Szily 交錯和**——ℤ₂ 分次計數；
  S(1,n) = 2C_n）。
* `[S-D-FlipSpec]` flip 圖譜：五邊形 flip 圖 ≅ C₅（特徵多項式相等）；
  N 邊形 flip 圖 (N−3)-正則、Catalan(N−2) 頂點、直徑 1,2,4,5,7（N=4..8）；
  tr A = 0、tr A² = 2·邊數。（Pournin：N ≥ 13 時直徑 = 2N−10。）

## 5. stwist —— 超扭結

* `[S-D-Parity]` 奇偶 p: G → ℤ₂ 是群同態；Koszul 號 σ(a,b) = (−1)^{p(a)p(b)}
  是 2-閉鏈（結合律）。
* `[S-T-SignClass]` σ 在 H²(G, 𝔽₂) 中**非平凡**（d ≤ 3 窮舉 δμ = σ 無解）。
* `[S-C-H2Betti]` **Betti 譜**：dim H^k((ℤ/2)^d, 𝔽₂) = C(d+k−1, k)
  （多項環 𝔽₂[x₁..x_d]；H¹ = d、H² = C(d+1,2)、H³ = C(d+2,3)）。
* `[S-T-SCenter]` 號代數（ω=0＋Koszul 號）**交換但不超交換**：
  中心 = 全空間、超中心 = 偶部（dim 2^{d−1}）。
* `[S-D-SuperCenterDecomp]` 一般餘閉鏈的超中心分解：
  **(rad ∩ 偶) ⊕ {奇 a : b_ω(a,·) = p}**（否決了天真的「超中心 = 中心」）。
* `[S-NEG-OddSuperCenter]` **否定性結果**：G = (ℤ/2)^d、ℓ = 2 時
  **奇超中心元素永不存在**——b_ω 是交錯雙線性形式 A，而 xᵀAx = 0 (mod 2)
  ⟹ Ax = 1 的解必為偶。此結論對餘邊界擾動（b_ω 不變）穩定。
* `[S-C-GrTrace]` 分次正則表示的超特徵標恆為 0（Witten 指標消失）、
  普通特徵標 = |G|·δ_{a,0}——譜上的「分次隱形」。

## 6. sgauge —— Clifford 超代數

* `[S-D-ClMono]` 單項 Clifford：γ_S·γ_T = (−1)^{inv(S,T)}q^{S∩T}γ_{S△T}；
  結合律、分次相容、{γᵢ,γⱼ} = 2δᵢⱼqᵢ。
* `[S-T-ClCenter]` 中心／反中心表：d 偶 (1,1)、d 奇 (2,0)
  （d 奇：中心 = span{1, ω}——矩陣實現中 ω ∝ I 可直接看見）。
* `[S-T-ClGrTensor]` **Cl(V⊕W) ≅ Cl(V) ⊗̂ Cl(W)**：全量結構常數比對，
  Koszul 叉號 (−1)^{|S₂||T₁|} 精確匹配 inv(S,T) 的交叉項。
* `[S-D-GammaSpec]` γ 矩陣譜恆等式：tr(γ_S) = 0（S ≠ ∅；d 奇的滿集例外）、
  ω² = (−1)^{d(d−1)/2}。
* `[S-D-LatDirac]` 格子 Dirac D = Σᵢγᵢ⊗A：**D² = d·(I⊗A²)**
  （交叉項 Koszul 相消的矩陣層面驗證）；手性 Π = i^{d/2}ω 僅 d 偶存在
  （d 奇：ω 中央）；**分次跡消失** tr(Π·D^{2k}) = 0（k ≥ 1）
  ——格子 SUSY 的 Witten 指標式敘述（由 ΠD = −DΠ 的循環性強迫）。

## 7. sradon —— Radon 譜化

* `[S-D-RadSpec]` 仿射平面 𝔽_n² 的有限 Radon 變換 R：
  **RᵀR = nI + J** ⟹ 譜 {n^(n²−1), (n²+n)¹}，
  charpoly(RᵀR) = (x−n)^{n²−1}(x−n²−n)、charpoly(RRᵀ) = xⁿ·(同)，
  n ∈ {2,3,5,7}。
* `[S-T-FBP]` **Sherman–Morrison 濾波** (nI+J)^{-1} = (1/n)I − (1/(n²(n+1)))J：
  有限 FBP 的**精確重構** f̃ = X·Rᵀ·Rf = f。
* `[S-C-GradedRad]` 奇偶帶號 R̃ = D·R：譜不變、帶號 FBP 仍精確。
* `[S-T-RadEnergy]` Parseval 型：Σ_lines (Rf)² = n·Σ_pts f² + (Σf)²。

## 8. smetric —— 度量譜化

* `[S-D-CycLap]` 環圖 Laplacian：0 單根（連通）、tr = 2n、tr(L²) = 6n、
  偶 n 的 λ_max = 4、相異特徵值數 = n/2 + 1。
* `[S-T-LapNullity]` **mod-p 譜論**：nullity L(C_n) = 1 + [p | n]
  （解 v_i = α + βi：β 自由 ⟺ p | n）。
* `[S-NEG-Cospectral]` **否定性結果**：K_{1,4} 與 C₄∪K₁ 同譜
  （charpoly = x³(x²−4)）但不同構、度量結構不同
  ⟹ **譜資料無法恢復度量**（譜 Gromov–Hausdorff 方向的失敗）。
* `[S-D-VRBar]` VR 條碼：r = 0 ⟹ β = (n,0)；r = 1 ⟹ β = (1,1)（圓圈誕生）。
* `[S-D-Hodge]` **Hodge 分解**：β₁ = dim ker(B₁ᵀB₁ + B₂B₂ᵀ)
  （帶號 mod p）與 VR 消去法一致（n = 4..8、r = 1,2）。

## 9. sevolve —— 超對稱演化 + 持久帳本

* `[S-D-SusyEvo]` D ↦ UDV（U、V 可逆）：rank／核維數／指標不變；
  行清零（rank 恰掉 1）時兩核同時 +1——**指標跳變相消**。
* `[S-T-EvoStr]` 分次共軛 Q ↦ GQG⁻¹（G 偶、么上三角）：
  **charpoly(Q²) 守恆**（相似性）、str(H^k) = 0 逐步成立。
  （注意：D ↦ UDV **不**守恆 charpoly(DᵀD)——除非 U 正交；
  這是被測試釘死的常見陷阱。）
* `[S-C-EvoLedger]` 演化記錄寫入 sledger 雜湊鏈：sled_verify 全鏈通過；
  篡改任一 payload ⟹ 驗證失敗（純函式：原帳本不受影響）。

## 10. 持久帳本（跨訊息／跨執行）

```
ledger/LEDGER.jsonl        # sha256 雜湊鏈（創世 + 9 條套件不變量）
ledger/superledger.sh      # append（冪等去重）| verify | show
moon run cmd/superledger   # 產生 JSONL（stdout）
moon run cmd/superledger -- --verify <行...>   # 驗證外部帳本
```

設計：wasm 目標無 fs API ⟹ 檔案落地由 shell 完成；
格式／雜湊／驗證全在 MoonBit（sledger）。
帳本內容為確定性函數（固定種子）；「持久」= LEDGER.jsonl 隨專案累積。

---

## 總表：否定性結果（誠實的失敗）

| 編號 | 被否決的命題 | 反例 |
|---|---|---|
| `[S-NEG-strPlain]` | 純體上 str(MN) = str(NM) | 非齊次塊矩陣 |
| `[S-NEG-BerField]` | 純體上有非平凡 Berezinian | b = c = 0 |
| `[S-NEG-FlowDet]` | 譜流 = ½Δsgn det | diag(−25,−4,20)→diag(−26,9,13) |
| `[S-NEG-SDet]` | OSL(1|1)³ 有非平凡四次不變量 | 公共核 = 0（Euler 阻礙） |
| `[S-NEG-OddSuperCenter]` | (ℤ/2)^d 上有奇超中心元素 | xᵀAx = 0 ⟹ 解必偶 |
| `[S-NEG-Cospectral]` | 譜決定度量（譜 GH） | K_{1,4} vs C₄∪K₁ |

## 總表：計算發現（先算後證）

| 編號 | 內容 |
|---|---|
| `[S-T-OddAlg]` | {D_E,D_F} = 完整 Euler（不是只有腿次數） |
| `[S-D-SuperCenterDecomp]` | 超中心 = (rad∩偶) ⊕ {奇 a: b_ω(a,·)=p} |
| `[S-T-FlowMorse]` | 譜流的正確公式是 Morse 指標變化 |
| `[S-D-vonSzily]` | 超卡特蘭 = ℤ₂ 分次交錯和 |
