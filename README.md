# tensorlab

七個數學結構，一套消元引擎。[MoonBit](https://www.moonbitlang.com) 實作，穩定版工具鏈。

| 文件 | 內容 |
|---|---|
| **[THEORY.md](THEORY.md)** | 定義 `[D-]` / 公理 `[Ax-]` / 命題 `[P-]` / 定理 `[T-]` / 推論 `[C-]` / 算法 `[E-]` / 演變恆定關係 `[Inv-]`，含 §11「被計算否決的猜想」與 §13 缺陷表 |
| **[CODE_HEALTH.md](CODE_HEALTH.md)** | 代碼健檢：除錯、去重、減債、清死碼的完整紀錄與可重跑證據 |
| [README.mbt.md](README.mbt.md) | 套件依賴圖、指令、測試分佈（MoonBit 套件說明） |

主題：**張量積 · 消元 · 扭曲 K 理論 · 非交叉樹 · 向量叢（格點線叢）· 拉蒙場（Clifford 零模）· Radon 變換 · 有限度量空間**，
以及把它們放在「演變」下仍成立的**恆定關係**。

```sh
export PATH="$HOME/.moon/bin:$PATH"
moon check          # 0 errors, 1 warning
moon test           # Total tests: 66, passed: 66, failed: 0
moon run cmd/main   # 92 行即時重算的報告
```

套件：`core`（F_p 消元、Smith 標準形、整數關係）→ `tensor` / `nc` / `twist`→`gauge` / `radon` / `metric` → `evolve` → `cmd/main`。

授權：Apache-2.0（見 [LICENSE](LICENSE)）。
