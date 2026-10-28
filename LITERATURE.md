# LITERATURE —— 超化／譜化擴充的文獻對照

本文件記錄 superlab 擴充所對照的文獻（2026-10 檢索），
以及「本實作的計算結果 ↔ 文獻命題」的對照表。
檢索透過網頁搜尋完成；以下各條給出來源連結與對應的實作測試。

---

## 1. 超矩陣：超跡與 Berezinian（score 套件）

* **Berezin 超代數（超跡、超行列式）**：
  * "Lectures on Super Analysis"（arXiv:1504.03049）——
    str 的定義與性質；sdet M = det(A − CB⁻¹D)·(det B)⁻¹。
    <https://arxiv.org/pdf/1504.03049>
  * "On the superdeterminant function for supermatrices"（Codreanu）——
    Berezinian 乘法性的嚴格證明，關鍵恆等式
    **det(1−PQ)·det(1−QP) = 1**（P、Q 為 Grassmann 奇部的矩形矩陣）。
    <https://www.researchgate.net/publication/231016040_On_the_superdeterminant_function_for_supermatrices>
  * Encyclopedia of Mathematics: Supersymmetry——
    str 消滅超交換子；**Ber(T^st) = Ber(T)**（超轉置不變）。
    <https://encyclopediaofmath.org/index.php/Supersymmetry>

**對照**：
`[S-T-Ber]`（Ber 乘法性）⟺ 上述乘法性定理；
`[S-T-strCyc]`（str 循環性）⟺ str 消滅超交換子；
`[S-T-ChPolyRel]` det(xI − DDᵀ) = x^{n−m}det(xI − DᵀD) 正是
det(1−PQ)det(1−QP) = 1 的特徵多項式版本；
`[S-NEG-BerField]` 與文獻一致：Berezinian 只在純體為平凡
（需要奇部以給出非平凡的 (1|1) 型行為）。

## 2. 譜流與 Morse 指標（spec 套件）

* Robbin–Salamon, **"The spectral flow and the Maslov index"**——
  有限維情形 **譜流 = 負特徵值個數之差**（index difference /
  "the dimension of the negative eigenspace ... the spectral flow can be
  expressed as the index difference"）；
  而 ½(sign A(b) − sign A(a)) 形式的公式屬於 **Maslov 指標**
  （路徑落在辛群／Lagrange 分裂的座標）。
  <https://webhomes.maths.ed.ac.uk/~v1ranick/papers/robbsala1.pdf>
* Waterstraat, "A K-Theoretic Proof of the Morse Index Theorem"
  （arXiv:1007.1190）——譜流 = Morse 指標差的 K-理論觀點。
  <https://kar.kent.ac.uk/51388/1/1007.1190v3.pdf>

**對照**：`[S-T-FlowMorse]`（flow = n₋(H₀) − n₋(H₁)）與 Robbin–Salamon
的有限維公式一致；`[S-NEG-FlowDet]` 的否定性結果因此有了解釋：
「½Δsgn det」是 **Maslov 型公式**，把它套在一般對稱矩陣路徑上
超出了其適用範圍——本實作的計算反例（diag(−25,−4,20)→diag(−26,9,13)）
正是兩者分歧的最小案例。

## 3. 非交叉分割與自由機率（snc 套件）

* Sagan, **"Möbius functions of lattices"**（Adv. Math. 127 (1997)；
  arXiv:math/9801009）——Kreweras 定理
  **μ(NC_n) = (−1)^{n−1}C_{n−1}**，並以 NBB 基給出組合解釋。
  <https://arxiv.org/pdf/math/9801009>
* Speicher, "Free Probability Theory and Random Matrices"（調查講義）——
  **自由矩-累積量公式** m_n = Σ_{π∈NC(n)} ∏ κ_{|B|}；
  Wigner 半圓律與 Marchenko–Pastur 的自由累積量刻劃。
  <https://www.math.uni-sb.de/ag/speicher/surveys/speicher/bielefeld.pdf>
* Wikipedia: Noncrossing partition——|NC(n)| = Catalan(n)、
  自由累積量在自由機率中的角色。
  <https://en.wikipedia.org/wiki/Noncrossing_partition>

**對照**：`[S-D-NCPart]`、`[S-T-MobiusNC]`（μ 的超積公式，
是 Kreweras 定理的逐 π 精緻化：[0̂,π] ≅ ∏ NC_{|B|}）、
`[S-D-FreeCum]`（r≡1 ⟹ m_n = Cat n = 秩 1 MP；r = e₂ ⟹ 半圓律 m_{2k} = C_k）
皆與 Speicher 的公式逐項一致。

## 4. 超卡特蘭數（snc 套件）

* Chen–Wang, "The super Catalan numbers S(m, m+s) for s ≤ 4"
  （UMN REU 報告）——von Szily 恆等式
  S(m,n) = Σ_k (−1)^k C(2m, m+k)C(2n, n−k)
  與 Gessel 正規化 S(m,n) = (2m)!(2n)!/(m!n!(m+n)!) 的整值性。
  <https://www-users.cse.umn.edu/~reiner/REU/ChenWang2012.pdf>

**對照**：`[S-D-vonSzily]` 以閉式 = 交錯和（mod 大素數）逐項驗證；
本實作補充的組合觀點：交錯和 = ℤ₂ 分次計數（超維數）。

## 5. Flip 圖直徑（snc 套件）

* Pournin, "The diameter of associahedra"（Adv. Math. 259 (2014)）——
  凸 N 邊形 flip 圖直徑 = 2N−10 當 **N ≥ 13**；
  Wikipedia: Flip graph（STJT 的大 N 漸近與 Pournin 的全部 N）。
  <https://en.wikipedia.org/wiki/Flip_graph>

**對照**：`[S-D-FlipSpec]` 計算的直徑 1,2,4,5,7（N=4..8）是 Pournin
定理範圍之外的精確小案例；N=13 的漸近值 16 未在本實作範圍
（C(27,10) 級的枚舉）——誠實記錄為邊界。

## 6. 有限 Radon 變換（sradon 套件）

* "Explicit oblique inverses of the approximate discrete Radon transform"
  （arXiv:2610.23363）——明確寫出：
  「有限 Radon 變換在 ℤ_p×ℤ_p 上，對 p(p+1) 條線
  {(x, mx+b)} 與 {(c,y)} 求和，任兩點恰共一線、每點恰在 p+1 條線上，
  **R^⊤R = pI + 11^⊤**」。
  <https://arxiv.org/html/2610.23363>
* Do–Vetterli, "The Finite Ridgelet Transform"（IEEE TIP）——
  FRAT/FBP：有限反投影與 (p+1)p−1 對角元之幾何。
  <https://minhdo.ece.illinois.edu/publications/FRIT_trans.pdf>

**對照**：`[S-D-RadSpec]` 的 RᵀR = nI + J 與譜 {n^{n²−1}, (n²+n)¹}
和 arXiv:2610.23363 完全一致；`[S-T-FBP]` 的 Sherman–Morrison
濾波精確重構是該框架的模 p 版本。

## 7. Vietoris–Rips 複形（smetric 套件）

* Adamaszek–Adams, "The Vietoris-Rips complexes of a circle"
  （Pacific J. Math. 290 (2017)）——
  VR(S¹; r) ≃ S^{2k+1}（2πk/(2k+1) < r ≤ 2π(k+1)/(2k+3)）。
  <https://www.researchgate.net/publication/273471446_The_Vietoris-Rips_complexes_of_a_circle>
* Adamaszek et al., "Vietoris–Rips and Čech Complexes of Metric Gluings"
  （SoCG 2018）——度量圖的 VR 持久同調。
  <https://drops.dagstuhl.de/storage/00lipics/lipics-vol099-socg2018/LIPIcs.SoCG.2018.3/LIPIcs.SoCG.2018.3.pdf>

**對照**：`[S-D-VRBar]` 在有限環 C_n（整測地距離）上觀察到
r=1 時 β = (1,1)（圓圈誕生）是 Adamaszek–Adams 定理的離散前奏
（有限 n 的 VR 在 r 增大時依序得到更高維球面的同倫型——
本實作僅驗證 r ≤ 2 的低維條碼）。

## 8. Clifford 代數與格子 Dirac（sgauge 套件）

標準內容（Berezin；Lawson–Michelsohn《Spin Geometry》的代數骨架）：
Cl(V⊕W) ≅ Cl(V)⊗̂Cl(W)（分次張量積）、
中心/反中心表（d 偶 (1,1)、d 奇 (2,0)）、手性算子僅 d 偽存在。
本實作 `[S-T-ClGrTensor]`、`[S-T-ClCenter]`、`[S-D-LatDirac]`
以全量結構常數與矩陣計算釘死這些標準事實，並補充分次跡
tr(ΠD^{2k}) = 0 的格子 SUSY 敘述（Witten 指標式論證）。

---

## 檢索方法備忘

* 檢索日期：2026-10-29；工具：網頁搜尋（關鍵詞組合）。
* 命中優先序：教科書/講義 > 期刊論文 > 百科（僅作交叉確認）。
* 每條文獻都對照到至少一個已通過的測試標籤（見 SUPER_THEORY.md）。
