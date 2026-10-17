# 论文结果覆盖表

此表按原 TeX 的具名 theorem/lemma/proposition/corollary 登记，共 26 项。机器来源是 `state/paper_coverage.json`，本表由 `tools/update_dashboard.py` 同步生成。页码是原 PDF 页码，TeX 行号仅辅助定位，label 为稳定定位。

初始 19 项工作目标只映射其中 15 项结果，其余 11 项保留待分解。一个结果可以对应多个 Lean 声明；同一正文结果在附录证明不重复计数。Section 8 实验复现不在形式化计数内。

| ID | 原文结果 | 标签 | PDF 页 / TeX 行 | 阶段 | 初始目标 | Lean 声明 |
| --- | --- | --- | --- | --- | --- | --- |
| P001 | Theorem 2.1 | `thm:main` | 10 / 525 | M5 | C010 | 待建立 |
| P002 | Corollary 2.2 | `cor:general-scales` | 11 / 599 | M5 | C011 | 待建立 |
| P003 | Corollary 2.3 | `cor:scales` | 11 / 617 | M5 | C012 | 待建立 |
| P004 | Lemma 3.1 | `lem:graph` | 11 / 647 | M3 | C005 | 待建立 |
| P005 | Lemma 3.2 | `lem:cell` | 13 / 789 | M3 | 待分解 | 待建立 |
| P006 | Lemma 3.3 | `lem:eulerMR` | 14 / 863 | M3 | C006 | 待建立 |
| P007 | Lemma 3.4 | `lem:frozen` | 15 / 964 | M3 | 待分解 | 待建立 |
| P008 | Theorem 3.5 | `thm:timeerror` | 16 / 1023 | M3 | C007 | 待建立 |
| P009 | Lemma 4.1 | `lem:spatialEuler` | 17 / 1148 | M4 | C008 | 待建立 |
| P010 | Theorem 4.2 | `thm:combined` | 19 / 1287 | M4 | C009 | 待建立 |
| P011 | Proposition 6.1 | `prop:p1` | 21 / 1499 | M6a | C014 | 待建立 |
| P012 | Proposition 6.2 | `prop:fd` | 23 / 1672 | M6a | C015 | 待建立 |
| P013 | Lemma 7.1 | `lem:physicalduality` | 24 / 1753 | M6b | 待分解 | 待建立 |
| P014 | Theorem 7.2 | `prop:physicalO` | 25 / 1827 | M6b | C016 | 待建立 |
| P015 | Theorem 7.3 | `prop:physicalC` | 27 / 2032 | M6b | C017 | 待建立 |
| P016 | Lemma 7.4 | `lem:filter-reverse` | 29 / 2164 | M6b | 待分解 | 待建立 |
| P017 | Theorem 7.5 | `thm:filtered-observability` | 29 / 2177 | M6b | C018 | 待建立 |
| P018 | Corollary 7.6 | `cor:filtered-control` | 29 / 2201 | M6b | 待分解 | 待建立 |
| P019 | Proposition 7.7 | `prop:filter-p1` | 30 / 2224 | M6b | 待分解 | 待建立 |
| P020 | Proposition 7.8 | `prop:filter-fd` | 30 / 2241 | M6b | 待分解 | 待建立 |
| P021 | Corollary 7.9 | `prop:control-convergence` | 31 / 2344 | M6c | C019 | 待建立 |
| P022 | Proposition A.1 | `prop:spatial-operators` | 36 / 2615 | M6a | 待分解 | 待建立 |
| P023 | Corollary A.2 | `prop:analytic-realizations` | 37 / 2659 | M6a | 待分解 | 待建立 |
| P024 | Proposition A.3 | `prop:continuousCE` | 37 / 2672 | M6a | C013 | 待建立 |
| P025 | Lemma B.1 | `lem:fd-boundary-affine` | 38 / 2803 | M6a | 待分解 | 待建立 |
| P026 | Lemma B.2 | `lem:fd-weighted-approximation` | 39 / 2841 | M6a | 待分解 | 待建立 |
