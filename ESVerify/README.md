# Erdős–Szekeres 立方根上界的 Lean 验证

项目目标是形式化验证 `ES(1).pdf` 中定理 1.1 的证明。对每个非空、无三点共线的有限平面点集 `P`，证明

\[
\log_2 |P| \le h(P) + C h(P)^{1/3},
\]

其中 \(h(P)\) 是凸位置子集的最大基数，\(C>0\) 是绝对常数。同时验证文中的 Erdős–Szekeres 数上界推论。

完成标准是 `lake build ESVerify` 成功，主定理通过 `#print axioms` 检查，且不含 `sorryAx`、新增公理或未解除的数学假设。正文所引用的结果需由 Mathlib 或本项目中的 Lean 定理给出。

## 验证入口

- `ESVerify.cube_root_bound` 是定理 1.1 的对数高度不等式。
- `ESVerify.esNumber_cube_root_bound` 是 Erdős–Szekeres 数上界。

在 Lean 4.31.0 下运行 `lake build ESVerify`。入口文件 `ESVerify.lean` 会打印这两条定理的公理依赖。

| 论文部分 | Lean 文件 |
| --- | --- |
| §2 平面链、终端秩与路径计数 | `Planar.lean`、`RankPaths.lean`、`PlanarRankPaths.lean` |
| §3 两直线等分与恒定连接秩 | `Equipartition.lean`、`PlanarEquipartition.lean`、`JoiningRanks.lean` |
| §4 链拼接与收缩二择一 | `ConvexChains.lean`、`ChainPieces.lean`、`RankAlternative.lean`、`JoiningAlternative.lean` |
| §5 秩差上界 | `RankWordAdapter.lean`、`RankDifference.lean` |
| §6 随机游走、浓缩与共同近似 | `KilledWalk.lean`、`Talagrand.lean`、`EnergyEntropy.lean`、`EnergyApproximation.lean` |
| §7 主定理与推论 | `Iteration.lean`、`Coordinates.lean`、`PlanarBound.lean`、`Theorem.lean`、`ErdosSzekeresNumber.lean` |

第 6 节用平方增量和表示单位线性插值的能量，在整数时刻验证第 5 节所需的一致逼近。覆盖数估计由自适应二分和有限编码证明。第 7 节用势函数的望远镜求和控制总损失。横坐标化简使用保持凸包和点数的可逆剪切。
