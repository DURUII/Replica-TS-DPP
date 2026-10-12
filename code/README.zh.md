# TS-DPP：实验复现

[English](README.md) | 中文

## 运行

> 在 Apple M4、macOS 26.2 (25C56)、Python 3.13.5 开发测试

实验参数遵循论文第五节：`theta_i ~ U[0,1]`、`gamma ~ Dirichlet` 且 `sum gamma = 1`、
`c_i ~ U[0.2, 0.5]`、`B = 0.35`。

论文合成实验运行 50 个 episode。本项目保存 100 个 episode，Fig. 3、Fig. 4 绘制前 50 个；Fig. 6、Fig. 7 使用完整长度。见[罚值偏移，增长比例接近](#difference-4)。

在 `code/` 目录执行：

```
pip install numpy scipy matplotlib markovianbandit-pkg numba
python src/run.py all          # simulations  -> results/*.csv
python src/plot/draw.py        # results/*.csv -> figs/*.png
python src/diagnose.py gaps    # the evidence behind "Differences" below
python src/diagnose.py whittle # why the Whittle baseline lands below the oracle
```

`markovianbandit-pkg` 未声明 `numba`、`scipy` 依赖，但加载时会导入两者，需显式安装。

## 差异概览

由于论文未提供实验代码，基线实现、数据切片及 episode 边界等处理细节也未说明。为检验这些选择是否造成差异，我们比较了不同基线实现、预算控制方式和边界处理，并核对原图读数与模拟数据。

| 编号 | 差异 | 摘要 |
| --- | --- | --- |
| 1 | [基线排序](#difference-1) | 合成实验中，采用 episode 重置和本项目推导的 Whittle index 后，Whittle 罚值低于 oracle，与论文 Fig. 3、Fig. 4 的排序相反。排序也随 episode 边界处理改变。 |
| 2 | [Whittle 基线](#difference-2) | 论文引用的 index 针对另一种 age 重置方式，未说明如何用于当前问题。直接使用引用公式可以得到论文报告的排序方向；但是，按当前问题推导二维 index 后，排序发生反转。 |
| 3 | [Lyapunov 基线](#difference-3) | 本项目以 posterior 均值运行 DPP 规则，Lyapunov 与 oracle 的差距小于论文报告值。尝试改用可观测 age 后，差距又过大；已检验的实现尚未同时重现差距方向与量级。 |
| 4 | [罚值量级与运行长度](#difference-4) | 从 N = 4 到 N = 8，罚值增长比例与论文接近，但绝对数值存在偏移。 |
| 5 | [Regret 的定义](#difference-5) | 论文未说明 time-averaged regret 如何归一化，以及采用哪个比较基准。本项目明确以 oracle 为基准，绘制累计 episode regret 的平均值；可以比较衰减趋势，纵轴数值不能直接对应。 |
| 6 | [真实数据与 episode 边界](#difference-6) | 论文未给出数据月份和切片方式。本项目按事件计数选取 2019 年 12 月三类事件，计数相差 0.44%。延续 age 状态能接近 Fig. 5 的形状和量级。 |
| 7 | [预算约束](#difference-7) | 在当前参数与实现下，不带预算 queue 的 Whittle 平均成本接近预算，带 queue 的 policy 则略低于预算。给 Whittle 加上相同 queue 后，其罚值优势仍存在。 |
| 8 | [估计偏差与区间覆盖率](#difference-8) | 估计仍有持续偏差；Beta 95% 后验区间的频率覆盖率随 episode 增加而下降。 |

## 差异细节

### 约定

| 符号或术语 | 含义 |
| --- | --- |
| `se` | 估计不确定性；数值越小，估计越精确 |
| 尾段罚值 | 最后 10 个 episode 的平均罚值 |
| `reset` | 每个 episode 开头重置 age |
| `carry` | episode 之间延续 age |

各基线均在转移概率未知的在线设定下运行。除已知真实参数的 oracle 外，其余 policy 使用 posterior 采样值或均值；带 virtual queue 的 policy 按式 (12) 控制预算。各项实现如下：

| Policy | 使用的参数 | arm 选择方式 |
| --- | --- | --- |
| Belief-DPP (oracle) | `theta*` | Eq. (13) |
| TS-DPP | 每个 episode 从 Beta posterior 中抽取一次 | Eq. (13) |
| Lyapunov [20] | posterior 均值 | Eq. (13) |
| Whittle [24] | posterior 均值 | [为本问题推导的 Whittle index](#difference-2)，`argmax gamma_i * I_i(x, y)` |

<a id="difference-1"></a>

### 1. 基线排序反转

#### 差异

原图 3、原图 4 罚值排序为：

```
TS-DPP ~ Belief-DPP (oracle)  <  Lyapunov [20]  <  Whittle [24]
```

本复现在合成实验中采用 episode 重置和二维 Whittle index，Whittle 罚值低于 oracle。

更换 index 对照见[Whittle index 依赖 age 重置方式](#difference-2)；延续 age 状态后，Whittle 罚值最高，见[Trace 切片与 episode 边界](#difference-6)。

#### 解释

oracle 是已知真实参数的 DPP policy，Whittle 则按另一种优化方式选择 arm。

#### 检验

##### 原图读数与配对检验

在 `L = 20, V = 0.2` 下，`python scripts/measure_fig_levels.py` 按各面板刻度读取原图；`python src/diagnose.py gaps` 给出相对 oracle 的配对罚值差距：

| Policy | 原图 3(a) `N = 4` | 原图 4(a) `N = 8` | 本复现 `N = 4`（200 次运行） |
| --- | --- | --- | --- |
| Lyapunov | `+1.71` | `+2.69` | `+0.42` (se 0.09) |
| Whittle | `+4.45` | `+8.40` | `-2.84` (se 0.25) |
| TS-DPP | `+0.01` | `+0.14` | `-0.25` (se 0.51) |

TS-DPP 与 oracle 相差不足半个标准误差；Lyapunov 差距方向与论文一致，量级约为原图 3(a) 的四分之一，见[Lyapunov 罚值差距未复现](#difference-3)。Whittle 全部八组参数中均低于 oracle，配对差距为 `-2.8` 至 `-4.7`，每组 200 次运行（`results/paired_gaps.csv`）。

##### 预算与真实参数对照

`python src/diagnose.py whittle` 固定 `reset`，分别给 Whittle 加入式 (12) 的 virtual queue、提供真实参数 `theta*`，结果如下（`results/whittle_ab.csv`）：

| 变体 | 尾段罚值 | 相对 posterior 均值 DPP | 相对 oracle | 实测成本 |
| --- | --- | --- | --- | --- |
| Belief-DPP (oracle)，已知 `theta*` | `77.21` | `-0.42` (se 0.09) | `+0.00` | `0.3467` |
| DPP，posterior 均值 | `77.63` | `+0.00` | `+0.42` (se 0.09) | `0.3471` |
| Whittle index，无预算项 | `74.37` | `-3.26` (se 0.25) | `-2.84` (se 0.25) | `0.3514` |
| Whittle index + 式 (12) queue | `74.47` | `-3.16` (se 0.25) | `-2.74` (se 0.25) | `0.3485` |
| Whittle index + queue，已知 `theta*` | `74.57` | `-3.06` (se 0.28) | `-2.64` (se 0.27) | `0.3484` |

加入 queue 后，Whittle 成本由 `0.3514` 降至 `0.3485`，相对 oracle 的罚值优势仍为 `2.74`；再提供 `theta*` 后，优势为 `2.64`。

#### 判断

在 `reset` 设定下，两项对照均保留 Whittle 的罚值优势。

<a id="difference-2"></a>

### 2. Whittle index 依赖 age 重置方式

#### 差异

论文引用 [24]（Hsu, Modiano, Duan），但未说明如何将其 Whittle index 用于当前模型。该文的闭式 index 为：

```
I(x) = x^2/2 - x/2 + x/p
```

公式见 Hsu 等，[Scheduling Algorithms for Minimizing Age of Information in Wireless Broadcast Networks with Random Arrivals](https://www.mit.edu/~modiano/papers/CV_J_110.pdf)，Theorem 17。

#### 解释

此公式对应采集后 age 重置为 `1` 的子问题。

本模型拉动 PoI Arm `a` 后，按式 (4) 设置 `Y_a := X_a + 1`，copy age 取决于当前 event age。

#### 检验

`python src/diagnose.py variants` 在相同 seed 下将各变体与 oracle 配对比较（`results/baseline_variants.csv`）：

| 变体 | 相对 oracle 的配对罚值差距 | 结果 |
| --- | --- | --- |
| Hsu 闭式公式，belief 状态 | `+70.7` (se 2.7) | 罚值较高 |
| Hsu 闭式公式，可观测 copy age | `+17.9` (se 1.6) | 罚值较高 |
| 本模型二维 arm 的 index | `-2.84` (se 0.25) | 罚值较低 |

`src/sim/whittle.py` 以 `(event age, copy age)` 为状态，分别给出拉动与不拉动 arm 时的转移概率和奖励，再调用 [`markovianbandit-pkg`](https://pypi.org/project/markovianbandit-pkg/) 计算各状态的 Whittle index。

subsidy 是“不拉动 arm 时给予的补偿”。补偿逐渐增大，不拉动会更有吸引力；当拉动与不拉动的最优长期收益相同时，这个临界补偿就是该状态的 Whittle index。index 较高，表示需要较多补偿才愿意放弃拉动该 arm。

包的当前实现采用 Gast、Khun、Gaujal 的算法，按 index 从小到大计算临界值，并检查 indexability：补偿增加时，最优选择为“不拉动”的状态集合是否只扩大。本项目调用 `whittle_indices()`；方法见 [Testing Indexability and Computing Whittle and Gittins Index in Subcubic Time](https://arxiv.org/abs/2203.05207)，Algorithm 2。

#### 判断

检验表明，age 转移方式和 index 实现足以改变基线排序。

<a id="difference-3"></a>

### 3. Lyapunov 罚值差距未复现

#### 差异

本复现的 Lyapunov 罚值比 oracle 高 `0.42`（se `0.09`），小于原图 3(a) 的 `1.71` 和原图 4(a) 的 `2.69`。论文引用 [20]，但未给出该基线在当前模型中的具体形式。

#### 解释

[20] 的 index 含分母 `(1 + phi_n(alpha) / lambda_n)`，涉及 frame length 和 idle 参数。

当前 arm 模型无对应参数，本复现采用未归一化的分子。

论文式 (13) 已是二次 Lyapunov 函数 `L(Z) = Z^2 / 2` 的 drift-plus-penalty 规则，因此本复现的 Lyapunov 与 oracle 共用式 (13)，分别使用 posterior 均值与真实参数 `theta*`。

#### 检验

`python src/diagnose.py variants` 比较了式 (16) 的 belief 与可观测 copy age 两种输入（`results/baseline_variants.csv`）：

| 式 (13) 的输入 | 相对 oracle 的配对罚值差距 |
| --- | --- |
| belief，posterior 均值 | `+0.42` (se 0.09) |
| 可观测 copy age | `+43.9` (se 1.8) |

#### 判断

改用可观测 copy age 后，罚值差距比论文约 `+2` 的差距高一个数量级。已检验的实现均未同时重现差距方向与量级，Lyapunov 基线差异尚未解决。

<a id="difference-4"></a>

### 4. 罚值偏移，增长比例接近

#### 差异

从 `N = 4` 到 `N = 8`，原图与复现罚值增长比例接近，但绝对数值存在偏移。

#### 解释

在 `N = 4` 时，复现均值与中位数相差 `5.6`（se `1.1`），提示少数高罚值样本影响均值。

`theta ~ U[0,1]` 下，稳态 event age 的跨参数期望 `E[(1 - theta) / theta]` 发散，极小 `theta` 可能造成长尾。有限时域截断了 age 增长，因而上述稳态计算只能提示均值敏感性。

论文说明 `m = 50` 个 episode，未说明独立抽取 `theta*` 的运行次数，量级偏移来源尚未确定。

#### 检验

原图 Fig. 3(a) 纵轴范围为 `65.6`–`78.8`，Fig. 4(a) 为 `86.5`–`103.2`，读数所用面板刻度间距为 `2.0`。按各面板刻度读取（`python scripts/measure_fig_levels.py`），与 `results/penalty_tails.csv` 中 oracle 结果比较：

| | Fig. 3(a), `N = 4` | Fig. 4(a), `N = 8` | 倍率 |
| --- | --- | --- | --- |
| 原图，Belief-DPP (oracle) | `66.74` | `87.89` | `1.32` |
| 复现，oracle 中位数 | `70.44` | `92.12` | `1.31` |
| 复现，oracle 均值 | `76.05` | `95.48` | `1.26` |

原图倍率为 `1.32`，复现中位数倍率为 `1.31`，相差 `0.01`；均值倍率为 `1.26`。复现均值比原图高 `9.3`、`7.6`，中位数高 `3.7`、`4.2`。若罚值随 `N` 翻倍，Fig. 4(a) 应约为 `133`，超过纵轴上限 `103.2`。罚值定义为 `sum_i gamma_i Y_i`，且 `sum_i gamma_i = 1`；加权平均本身不要求罚值与 arm 数成正比。

#### 判断

增长比例接近，绝对罚值偏移尚待解释。

论文 Fig. 3、Fig. 4 绘至第 50 个 episode。`src/plot/draw.py` 使用相同的 0..50 窗口；CSV 保存 100 个 episode，供 Fig. 6、Fig. 7 使用。调整 `HORIZON` 可改变绘图窗口。

<a id="difference-5"></a>

### 5. Regret 定义不明

#### 差异

论文未说明 Fig. 6 的 time-averaged regret 如何归一化，也未明确比较基准。原图与复现图的纵轴数值因而无法直接对应。

#### 解释

平均 regret 的数值取决于比较基准和归一化方式。本项目明确采用 oracle，并按 episode 数求累计平均。

#### 检验

##### 原图读数

`python scripts/measure_fig_levels.py` 读取 Fig. 6：第 1 个 episode 的五条曲线介于 `2264`–`3925`，其中四条为 `V = 0.5, 1, 5, 10` 下的 TS-DPP。图例将两条曲线均标作 `L = 20, V = 0.5`；依据正文关于所建立上界的说明，本项目将虚线辨认为定理上界。

Fig. 5 的真实数据实验取 `N = 3, L = 20`，逐 episode 罚值约为 `60`–`200`：最低首点为 `63.2`，最高平台为 `190.3`。Fig. 6 首点约为 `200` 的 `11`–`20` 倍，或每 slot 罚值 `10` 的 `226`–`392` 倍。这些数值显示两图量级相距甚远；Fig. 6 采用合成设定，Fig. 5 读数无法为其罚值设上界，regret 定义仍待论文补充。

##### 复现定义与结果

本项目以 oracle 为比较基准，绘制累计 episode 贝叶斯 regret 的平均值：

```
Delta_l          = E_{theta*}[ pen_l(policy) ] - E_{theta*}[ pen_l(oracle) ]
time-averaged(l) = (1/l) * sum_{j<=l} Delta_j
```

定理 2 上界含未指定常数，绘图时将其缩放至与经验曲线共用第 1 个 episode 锚点。该比较展示衰减趋势：经验值在第 100 个 episode 降至 `0.53`，缩放后的界为其 `2.3` 倍，最大倍率为 `2.8`。比较针对归一化后的衰减趋势；原定理上界常数仍未确定。

复现的四条 `V` 曲线接近重合。端点为 `0.535`（`V = 0.5`）与 `0.563`（`V = 1`），所报告端点变化小于 6%，与估计误差主导 regret 的解释相符。原图四条 TS-DPP 曲线首点介于 `2264`–`3578`，平台介于 `19`–`116`，相差约六倍；正文描述四条曲线均收敛。若比较基准采用随 `V` 改变的最优 policy，regret 对 `V` 的依赖也可能改变。论文未说明这一选择，归一化与比较基准均待确定。

<a id="difference-6"></a>

### 6. Trace 切片与 episode 边界

#### 差异

论文 Fig. 3、Fig. 4、Fig. 6 使用合成设定；Fig. 5 使用真实 trace，取 `V ∈ {0.04, 0.06, 0.08, 0.10}`。

参考文献 [31] 给出 Kaggle 数据集地址，但未说明月份、文件版本、窗口选择或 episode 边界处理。

本项目按事件计数选取 2019 年 12 月三类事件，并延续 episode 间 age 状态，得到接近 Fig. 5 的形状与量级。

#### 解释

##### 切片依据

论文将时间戳映射至 1 秒时隙，排除一种低频事件后保留三种，共计 `1,654,771` 次。按这一描述，本项目将同类事件在同一秒内的多次发生合并。对五个月文件、四种事件的二至四类型子集，分别统计行数、非空时隙、去重用户及 `(user, item)` 对，比较如下：

| 切片 | 计数 | 偏差 | 相对偏差 |
| --- | --- | --- | --- |
| 2019-Dec `view` + `cart` + `remove_from_cart`，非空时隙 | 1,647,519 | −7,252 | −0.44% |
| 2019-Oct `view` + `cart` + `purchase`，非空时隙 | 1,645,164 | −9,607 | −0.58% |
| 2020-Jan `view` + `purchase`，去重 `(user, item)` | 1,662,767 | +7,996 | +0.48% |
| 2019-Dec `cart` + `remove_from_cart` + `purchase`，行数 | 1,804,955 | +150,184 | +9.1% |

首行同时符合三类事件要求与小于 0.5% 的计数偏差。12 月 `purchase` 占 `29,137` 个非空秒，其余三类各占至少 `422,184`；另外四个月的三类高频事件计数均至少为 `1,717,728`。这些结果支持选取 12 月 `view`、`cart`、`remove_from_cart`，但尚未确定论文原切片。当前五个文件日期均为 `2020-03-16`；数据快照不同可能解释剩余 `0.44%` 偏差。

仓库内 `data/2019-Dec-3types.npz` 可核对首行计数。其余三行、`purchase` 计数、其他月份计数及文件日期，依据原始月度 CSV 的一次读取；原文件未随仓库提供。

##### 回放设置

trace 给出 `theta_hat = (0.4391, 0.2702, 0.1576)`，依次对应 `view`、`cart`、`remove_from_cart` 的每秒非空时隙比例。`gamma`、`c`、`B` 沿用第 V-A-1 节适用于全部模拟的配置：Dirichlet 且 `sum gamma = 1`、`U[0.2, 0.5]`、`0.35`。直接回放保留事件突发性，比 `Bernoulli(theta_hat)` 重采样更接近原图量级。论文仅在 Fig. 6 给出 Monte Carlo 样本数 `1000`，未说明 Fig. 5 运行次数。本复现取 `1000` 次，每次重新抽取 instance，四个 `V` 共用同一抽样，保持面板配对。

#### 检验

固定 trace、`theta_hat` 与其他参数，仅改变 episode 间 `X, Y` 处理。oracle 已知真实参数，无需学习，其曲线可隔离 age 预热影响。`V = 0.06` 下结果与原图 Fig. 5(b) 比较如下：

| `X, Y` 边界处理 | episode 1 | episode 5 | 平台 | 首点 / 平台 |
| --- | --- | --- | --- | --- |
| 重置为 0，oracle | 96.9 | 98.2 | 98.7 | 0.981 |
| 延续，oracle | 96.9 | 151.1 | 154.6 | 0.627 |
| 原图 Fig. 5(b)，TS-DPP | `63.2` | `124.5` | `145.9` | `0.43` |
| 原图 Fig. 5(b)，Lyapunov | `69.9` | `133.3` | `155.5` | `0.45` |
| 原图 Fig. 5(b)，Whittle | `83.0` | `150.1` | `173.2` | `0.48` |

前两行来自 `python src/diagnose.py carry`，该命令报告全部 `V`；后三行由 `python scripts/measure_fig_levels.py` 读取。原图未绘制 oracle。

两种处理均在 episode 开头清零 virtual queue `Z`，与式 (7) 的逐 episode 平均成本约束对应。另行延续 `Z` 时，诊断中 queue 持续增长，`V = 0.06` 的罚值在第 100 个 episode 达到 `321`，仍呈上升趋势；无 queue 的 Whittle 保持有界。`simulate` 的 `carry` 开关因此只延续 `X, Y`。

延续 `X, Y` 后，无需调整事件率，各 policy 平台接近原图：Lyapunov 为 `154.4` 对 `155.5`，TS-DPP 为 `155.4` 对 `145.9`，Whittle 为 `188.0` 对 `173.2`（`results/realworld_curves.csv`）。固定数据下 oracle 平台从约 `99` 增至 `154.6`，说明 age 边界处理能解释相当一部分量级偏移。

合成实验采用相同 `carry` 设置时，Whittle 排序与原图一致，但曲线转为上升：`N = 4, L = 20, V = 0.2` 下，oracle 与 TS-DPP 的首点 / 平台均为 `0.57`，原图 Fig. 3、Fig. 4 则下降。所检验的两种边界设置均未同时重现合成图与真实数据图形状。本项目据此对合成实验采用 `reset`，对连续 trace 采用 `carry`。Whittle 在 `reset` 下罚值最低，在 `carry` 下最高；[基线排序反转](#difference-1) 的排序反转也受边界选择影响。

#### 判断

Fig. 5 复现首点仍偏高，恢复也更快：TS-DPP 首点 / 平台为 `0.67`，原图为 `0.43`；Lyapunov 为 `0.65` 对 `0.45`。第 5 个 episode 比值分别为 `1.02`、`0.98`，原图为 `0.85`、`0.86`。

20 slot 内 age 重建过程可能受 trace 窗口位置影响，论文未说明窗口选择。切片计数另有 `0.44%` 偏差。以上检验确定了本实现对边界处理的敏感性，论文实际切片与边界约定仍待确定。Fig. 5 四个面板均以 Whittle 罚值最高，与原图排序一致；[基线排序反转](#difference-1) 仅涉及 Fig. 3、Fig. 4。

##### 数据来源与重建

数据来自 REES46 Marketing Platform，由 Michael Kechinov 在 Kaggle 发布为 [`mkechinov/ecommerce-events-history-in-cosmetics-shop`](https://www.kaggle.com/datasets/mkechinov/ecommerce-events-history-in-cosmetics-shop)，许可标注为 “Data files (c) Original Authors”。`data/2019-Dec-3types.npz` 保存 2019 年 12 月三类事件的按秒位图，供 Fig. 5 直接回放。提取程序为 `src/sim/extract.py`，原始月度文件未随仓库分发。下载并重建：

```
curl -L -o cosmetics.zip \
  "https://www.kaggle.com/api/v1/datasets/download/mkechinov/ecommerce-events-history-in-cosmetics-shop"
unzip -d cosmetics cosmetics.zip                        # five monthly CSVs, 2019-Oct to 2020-Feb
python src/sim/extract.py cosmetics/2019-Dec.csv.gz     # -> data/2019-Dec-3types.npz
```

<a id="difference-7"></a>

### 7. 预算控制降低平均成本

#### 差异

在当前参数与实现下，不带 virtual queue 的 Whittle 平均成本接近预算 `B = 0.35`；带 queue 的三种 DPP policy 略低于预算。

#### 解释

论文将 `B` 设为均匀随机选择 arm 的期望成本。由 `c_i ~ U[0.2, 0.5]`，跨 instance 的期望成本为 `0.35`。选择规则若与成本独立，也具有这一跨 instance 期望；单个 instance 的成本仍可高于或低于预算。Whittle [24] 未规定预算控制，本实现因而不带 queue；其余 policy 按式 (12) 更新 queue。

#### 检验

`python src/diagnose.py cost` 在相同的 200 个 instance 上比较平均成本：

| Policy | 实际平均成本 | 标准误差 | `(均值 − B) / 标准误差` |
| --- | --- | --- | --- |
| Belief-DPP (oracle) | `0.3467` | `0.0036` | `-0.9` |
| TS-DPP | `0.3469` | `0.0036` | `-0.9` |
| Lyapunov [20] | `0.3471` | `0.0036` | `-0.8` |
| Whittle [24]，无 queue | `0.3514` | `0.0035` | `+0.4` |

Whittle 均值高于预算 `0.4` 个标准误差；三种 DPP policy 则低于预算约 `0.8%` 至 `0.9%`。配对比较结果见 `results/cost_paired.csv`：Whittle 比 TS-DPP 多支出 `0.0045`（标准误差 `0.0012`，t 值 `3.8`），比 Lyapunov 多 `0.0044`，比 oracle 多 `0.0048`（标准误差 `0.0013`，t 值 `3.7`）。

给 Whittle 加入相同 queue 后，其成本从 `0.3514` 降至 `0.3485`，相对 oracle 的罚值差由 `-2.84` 变为 `-2.74`，见[基线排序反转](#difference-1)。

#### 判断

本实验中，queue 降低了平均成本。Whittle 跨 instance 平均成本接近预算；各 instance 是否满足约束还需单独检验。加入 queue 后，Whittle 罚值仍低于 oracle，成本差异只能解释部分罚值差距。

<a id="difference-8"></a>

### 8. 估计偏差持续，区间覆盖率下降

#### 差异

复现图 7 中，点估计从先验附近趋近真值；重复模拟则显示，估计仍有偏差，Beta 区间包含真值的频率随 episode 增加而下降。

#### 解释

论文将阴影带称为 Beta 分布的 95% confidence interval。本复现取式 (14) 所维护 `Beta(alpha, beta)` 的 2.5 与 97.5 百分位，点估计与区间均由 `model.posterior_path` 给出。这是该 Beta 分布的 95% 等尾可信区间；95% 指后验概率质量，固定 `theta*` 下的频率覆盖率需另行检验。

边界处理改变 posterior 更新。`simulate` 每个 episode 都将 `t_prev`、`s_prev` 清零；被拉动 arm 的首次观测因此使用截断的历史。若 age 同时重置，该次观测满足 `s <= t - 1 < n_gap = t`，式 (14) 必有 `I = 1`，并按观测 age 增加 `beta`。若延续 age，且它超过 episode 内经过的时间，则 `I = 0`；由于 `s_prev = 0`，整个延续 age 都计入 `beta`。后者改变了首次观测的成功指示与失败计数。

#### 检验

`python src/diagnose.py fig7` 固定三个 `theta*`，运行 300 次模拟，统计区间包含真值的频率（`results/fig7_calibration.csv`）。下表采用 `posterior_path` 绘图所用的 `reset`：

| Episode | `theta* = 0.239` | `0.489` | `0.839` |
| --- | --- | --- | --- |
| 20 | 86.3% | 91.7% | 94.0% |
| 50 | 74.3% | 84.3% | 92.0% |
| 100 | 65.7% | 77.7% | 81.0% |

从 episode 20 到 100，三个参数处的平均区间宽度缩小 `28%` 至 `34%`；`theta* = 0.239`、`0.839` 处 RMSE 仅下降 `4.5%`、`6.1%`。在 `0.489` 处，RMSE 下降 `46%`，区间宽度缩小 `34%`，覆盖率仍下降 `14` 个百分点。区间宽度与 RMSE 的相对变化不足以单独解释覆盖率。

复现图 7(b) 的单次轨迹也未覆盖真值：episode 20、100 的 `ci_low` 分别为 `0.5117`、`0.5095`，均高于 `theta* = 0.489`（`results/estimates.csv`）。

Episode 100 的平均估计偏差依次为 `+0.045`、`+0.012`、`-0.025`，约为 `4` 至 `10` 个标准误差。`python src/diagnose.py eq14` 改用轮询拉动，排除 arm 选择规则的影响（`results/eq14.csv`）。在 `theta = 0.239` 处，每 arm 拉动 6,400 次后偏差为 `+0.0397`（标准误差 `0.0006`）；拉动 25,600 次后为 `+0.0396`（标准误差 `0.0002`）。拉动次数增至四倍，偏差基本不变，`偏差 × 拉动次数` 从 `253.8` 增至 `1014.3`；另两个参数也呈现持续偏差。

固定间隔 `g` 的解析检验给出以下期望增量：

```text
E[Δalpha]        = 1 - (1 - theta)^g
E[Δalpha+Δbeta]  = sum_{s<g} (1 + s) theta (1 - theta)^s
                  + g (1 - theta)^g
E[Δalpha] / E[Δalpha+Δbeta] = theta
```

在检验的所有 `g`、`theta` 组合中，最后一式的数值误差不超过 `3e-17`。这项检验验证期望增量比例；有限样本估计偏差由上述重复模拟检验。

边界配对检验中，`theta = 0.239` 的偏差随 `reset` 改为 `carry` 从约 `+0.042` 变为 `-0.023`。100 个 episode、同一个 seed 下，`reset` 比 `carry` 使第一个 arm 的 `alpha` 多 `56`、`beta` 少 `211`；20 个 seed 的平均差分别为 `59`、`238`。轮询诊断中每 arm 每 episode 均有一次首次观测，故每 `L` 次拉动中有 `N` 次边界首次观测；增加 episode 不会降低这一比例。

#### 判断

这些检验显示，本实现中边界历史重置伴随持续估计偏差，区间收窄时频率覆盖率下降。`reset`、`carry` 的轮询诊断均有偏差，方向相反。论文未说明原图 7 的边界处理，尚不能确定原图采用哪种约定。
