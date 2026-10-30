# tensorlab

二十個數學結構，一套消元引擎。[MoonBit](https://www.moonbitlang.com) 實作，穩定版工具鏈。

| 文件 | 內容 |
|---|---|
| **[THEORY.md](THEORY.md)** | 定義 `[D-]` / 公理 `[Ax-]` / 命題 `[P-]` / 定理 `[T-]` / 推論 `[C-]` / 算法 `[E-]` / 演變恆定關係 `[Inv-]`；含 §11「被計算否決的猜想」、§13 缺陷表、**§14 超化 / §15 譜化 / §16 正則表示 / §17 賬本 / §18 五關係 / §19 譜序列 / §20 塞爾 / §21 Adams / §22 格羅滕迪克拓撲 / §23 凝聚 / §24 扭曲 AHSS / §25 交叉運算 / §27 導出張量積** |
| **[CODE_HEALTH.md](CODE_HEALTH.md)** | 代碼健檢：除錯、去重、減債、清死碼的完整紀錄與可重跑證據（第一輪 + 第二輪 §5 + **第三輪 §6**） |
| [README.mbt.md](README.mbt.md) | 套件依賴圖、指令、測試分佈（MoonBit 套件說明） |

主題：**張量積 · 消元 · 扭曲 K 理論 · 非交叉樹 · 向量叢（格點線叢）· 拉蒙場（Clifford 零模）· Radon 變換 · 有限度量空間**，
再把每個結構做**超化**（乘積 → 結果集）與**譜化**（結構 → 特徵多項式／譜），
放進**超級持久賬本**，最後用**相對／對偶／對比／蘊含／比率**五種關係導出擴展定理與算法。

```sh
export PATH="$HOME/.moon/bin:$PATH"
moon check          # 0 errors, 0 warnings
moon test           # Total tests: 144, passed: 144, failed: 0
moon run cmd/main   # 163 行即時重算的報告（13 + 7 個區段）
```

套件：`core`（F_p 消元、Smith 標準形、整數關係）→ `tensor` / `nc` / `twist`→`gauge` / `radon` / `metric` → `evolve`
→ `hyper`（超化）→ `spectral`（譜化、正則表示）→ `ledger`（超級持久賬本）→ `relations`（五關係）
→ **`cellcx`（CW 複形 + 持續條碼）→ `ss`（譜序列引擎）→ `serre`（塞爾）→ `adams`（Adams/Ext）→
`grotop`（格羅滕迪克拓撲）→ `condensed`（凝聚群、固態性）→ `ahss`（扭曲 AHSS）→ `dtensor`（導出張量積/Tor）→ `xops`（交叉運算）** → `cmd/main`。

三條橫切的「新定理」：

1. **秩律即絕對差律**（§14.3）：矩陣秩的超化與 `|a−b| ≤ c ≤ min(n, a+b)` 逐格相同 —— 兩條獨立路徑給出同一張表。
2. **譜不決定結構、跡才分離單位元**（§15.3、§16）：`K_{1,4}` 與 `C₄⊔K₁` 鄰接譜相同（直徑 2 vs ∞）；
   而 `tr ρ_reg` 一次就把群元素分開。
3. **扭轉可見性由 H³ 與維數共同決定**（§24、§25）：`H³ = 0` 或 `dim X ≤ 5` ⟹ twist 不可見；
   局部 twist 能否黏成整體類，由格羅滕迪克拓撲上的 `k¹ − r⁰` 給出可計算判準。
4. **不變量可以「被導出 → 被記錄 → 被稽核」**（§9 + §17 + §18）：消元導出守恆律、雜湊鏈保存它、五關係擴展它。

授權：Apache-2.0（見 [LICENSE](LICENSE)）。
