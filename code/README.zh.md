# TS-DPP 复现：面向不确定事件捕获的信息年龄感知移动群智感知

[English](README.md) | 中文

> 在 Apple M4、macOS 26.2 (25C56)、Python 3.13.5 上开发并测试。

## 概述

对以下论文中实验的复现：

```
@inproceedings{zhou2026age,
  title={Age-of-Information-Aware Mobile Crowdsensing for Uncertain Event Capture},
  author={Zhou, Jinrui and Xu, Yin and Xu, Haotian and Xiao, Mingjun and Wu, Jie},
  booktitle={IEEE INFOCOM 2026 - IEEE Conference on Computer Communications},
  pages={1--10},
  year={2026},
  organization={IEEE},
  doi={10.1109/INFOCOM59046.2026.11571737}
}
```

论文把不确定事件捕获建模为一个带未知转移概率的受限 episodic restless bandit，并提出
**TS-DPP**：一种将 belief-Drift-Plus-Penalty bandit 策略与 Thompson sampling 相结合的
方法。

所有参数均逐字照搬：`theta_i ~ U[0,1]`、`gamma ~ Dirichlet` 且 `sum gamma = 1`、
`c_i ~ U[0.2, 0.5]`、`B = 0.35`，以及第 V-A-2 节的各基线。论文的合成设定运行 `m = 50`
个 episode；本复现模拟 100 个并保存每一个 episode，因此 `draw.py` 从同一份 CSV 中绘制
论文的 0..50 窗口。见差异 4。

```
pip install numpy scipy matplotlib markovianbandit-pkg numba
python src/run.py all          # simulations  -> results/*.csv
python src/plot/draw.py        # results/*.csv -> figs/*.png
python src/diagnose.py gaps    # the evidence behind "Differences" below
python src/diagnose.py whittle # why the Whittle baseline lands below the oracle
```

`markovianbandit-pkg` 在其元数据中未声明任何依赖，但在加载时会 import `numba` 和
`scipy`，因此这两者必须显式安装。

Fig. 5 还需要真实世界的 trace，本仓库把它精简为 `data/2019-Dec-3types.npz`（0.8 MB：
三张按秒的事件位图）。`run.py all` 直接使用该文件。要从原始数据集重建它，见差异 6。

## 实验结果

Fig. 3 复现：逐 episode 的 penalty 趋势，`N = 4`。

![Fig. 3](figs/fig3.png)

Fig. 4 复现：逐 episode 的 penalty 趋势，`N = 8`。

![Fig. 4](figs/fig4.png)

Fig. 5 复现：真实世界设定。

![Fig. 5](figs/fig5.png)

Fig. 6 复现：时间平均 regret。Fig. 7 复现：参数估计趋势。

![Fig. 6](figs/fig6.png)
![Fig. 7](figs/fig7.png)

| 图 | 结果 |
| --- | --- |
| Fig. 3, Fig. 4 | 曲线与形状已复现；基线排序未复现，见差异 1 |
| Fig. 5 | 已从论文自己的 trace 切片复现；第 1 个 episode 偏浅，见差异 6 |
| Fig. 6 | 衰减率已复现；纵坐标是另一个量，见差异 5 |
| Fig. 7 | 趋势已复现；阴影带比 95% 覆盖率更窄，见差异 8 |

## 与论文的差异

本复现在文本允许的范围内尽可能贴近论文声明的设定。论文未发布任何代码、任何 artifact，
也未为其基线给出任何伪代码，因此文本留下了若干实现选择上的余地。以下每一项都陈述该歧义、
本复现所做的选择，以及该选择改变了什么。

每一次模拟都在论文自己的在线设定中运行全部基线，而不是在各基线自己的论文所假设的已知
动力学设定中运行。因此全部四条策略共享同一个 posterior，三条带 queue 的策略共享同一个
virtual queue，而它们中的三条共享同一条 arm 选择规则：

| Policy | `theta` used | arm-selection rule |
| --- | --- | --- |
| Belief-DPP (oracle) | `theta*` | Eq. (13) |
| TS-DPP | 每个 episode 从 Beta posterior 中抽取一次 | Eq. (13) |
| Lyapunov [20] | posterior 均值 | Eq. (13) — 同一条规则 |
| Whittle [24] | posterior 均值 | 差异 2 的二维 index，`argmax gamma_i * I_i(x, y)` |

这是对基线最宽容的读法，也是对论文最不利的读法：论文自己对这批先前工作的批评是，它们
假设了已知动力学、已知状态，或者不含 cost 约束，而这些不利条件在这里没有一个保留下来。
剩下的是 policy 结构，而差异 1 争的正是这一点。

### 1. Fig. 3 与 Fig. 4 中的基线排序是反的

这是唯一一处触及论断、而非绘图细节的差异。其中有一部分根本不是关于 policy 结构的论断：
Whittle 那一项随差异 6 的 episode 边界选择而变，`reset` 下最低、`carry` 下最高，因此请把
那一节与本节合起来读。

论文的 Fig. 3 和 Fig. 4 在每个面板中都显示：

```
TS-DPP ~ Belief-DPP (oracle)  <  Lyapunov [20]  <  Whittle [24]
```

在 `L = 20, V = 0.2` 处按已发表面板各自的刻度去读，得到下面两个 arm 数下的差距
（`python scripts/measure_fig_levels.py`）。本复现给出的是：

| Policy | 论文 Fig. 3(a) `N = 4` | 论文 Fig. 4(a) `N = 8` | 本复现（配对差距，200 次运行） |
| --- | --- | --- | --- |
| Lyapunov | `+1.71` | `+2.69` | `+0.42` (se 0.09) |
| Whittle | `+4.45` | `+8.40` | `-2.84` (se 0.25) |
| TS-DPP | `+0.01` | `+0.14` | `-0.25` (se 0.51) |

只有 Lyapunov 一项在符号上与论文一致：Lyapunov 落在 oracle 之上。TS-DPP 落在 oracle 的
半个标准误之内，在它两侧，因此它在这里的符号是噪声，论文的 `+0.01` 也没有被以任何方向
否定。这里的 Lyapunov 差距约为已发表值的四分之一，这是差异 3。Whittle 一项是反的，而且
这一点在全部八个 cell 中都成立（配对差距 `-2.8` 到 `-4.7`，每个 200 次运行），因此它
不是噪声。

**index 就是全部解释。** `python src/diagnose.py whittle` 通过逐一关闭另外两个嫌疑因素来
排除它们：

| Variant | Tail penalty | vs. TS-DPP | vs. oracle | Realised cost |
| --- | --- | --- | --- | --- |
| Belief-DPP (oracle), `theta*` known | `77.21` | `-0.42` (se 0.09) | `+0.00` | `0.3467` |
| TS-DPP | `77.63` | `+0.00` | `+0.42` (se 0.09) | `0.3471` |
| Whittle index, no budget term | `74.37` | `-3.26` (se 0.25) | `-2.84` (se 0.25) | `0.3514` |
| Whittle index + Eq. (12) queue | `74.47` | `-3.16` (se 0.25) | `-2.74` (se 0.25) | `0.3485` |
| Whittle index + queue, `theta*` known | `74.57` | `-3.06` (se 0.28) | `-2.64` (se 0.27) | `0.3484` |

额外开销不是解释：给 Whittle policy 同一个 virtual queue，会把它的 cost 拉回到与其他所有
策略相同的水平，却让 `-2.84` 中的 `-2.74` 依然成立。知道 `theta*` 也不是解释。剩下的是
policy 结构，而它有一个真实的理由：论文的 oracle 不是最优 policy。它就是式 (13) 的
drift-plus-penalty 规则在状态已知时的形式——在 *DPP family 内部*最优，而不是在全部
policy 上最优。Whittle index 求解的是平均回报松弛问题，而在这个 arm 上它找到了比式 (13)
更好的调度。一个学到的 policy 打败一个已知状态的 policy，只有在那个已知状态的 policy
最优时才构成矛盾。

论文的 Fig. 3 关于它自己的 Whittle 基线仍可能是对的，因为它的基线很可能不是这个 index
——见差异 2。

### 2. Whittle 基线含义不明确，且已发表的 index 无法迁移

论文引用 [24]（Hsu, Modiano, Duan），其 index 是闭式的：

```
I(x) = x^2/2 - x/2 + x/p
```

*Hsu, ISIT 2017, Thm. 7; extended in IEEE TMC 19(12), 2019, Thm. 17.*

该 index 是为这样一个子问题推导的：服务某个 arm 会把该 arm 的 age 重置为 `1`。而在本
模型中，拉动 PoI `a` 反而设置 `Y_a := X_a + 1`（式 4）——它装入的是当前记录在案的任何
事件，而该事件可能已经过期。这两个子问题并不同构，而且该公式指向了错误的方向：它去追逐
最陈旧的事件。

`python src/diagnose.py variants` 直接检验了这一点。每个变体共用相同的 seed，并在同一次
rollout 中与 oracle 比较：

| Variant | Paired gap vs. oracle | Verdict |
| --- | --- | --- |
| Hsu's closed form, belief state | `+70.7` (se 2.7) | 比 oracle 差 |
| Hsu's closed form, observed copy age | `+17.9` (se 1.6) | 比 oracle 差 |
| Index derived for this model's 2-D arm | `-2.84` (se 0.25) | 比 oracle 好 |

逐字套用 Hsu 的公式可以复现论文排序的 *方向*——Whittle 曲线明显落在 oracle 之上，与已
发表的图一致。而为本模型实际的 arm 推导 index 则会把它反转过来。本复现采用推导出的
index，因此这里的 Whittle 曲线与论文的曲线不同是预期之中的。

该 arm 是二维的，`(event age x, copy age y)`，正是因为一次拉动装入的是 `X + 1` 而不是
重置为 `1`。`src/sim/whittle.py` 构建该 arm，并把 subsidy 的二分求解交给
`markovianbandit-pkg`。

### 3. Lyapunov 基线定义不足，而式 (13) 本身就是 DPP 规则

[20] 中印出的 index 除以 `(1 + phi_n(alpha) / lambda_n)`。这里的 arm 不带有 frame length
或 idle 参数，因此本复现使用未归一化的分子。

更重要的是，论文的式 (13) *就是*二次 Lyapunov 函数 `L(Z) = Z^2 / 2` 的
drift-plus-penalty 规则，被化简为逐 arm 的闭式形式。因此对 [20] 的忠实实现必然会与
oracle 打平，而不是输给它，事实也确实如此：`+0.42` (se 0.09)。

要产生论文中的 `+2` 差距，需要对可观测的 copy age 而非式 (16) 的 belief 建 index，但该
变体落在 `+43.9` (se 1.8)，超出了一个数量级。我们未能找到同时复现论文 Lyapunov 差距的
方向与量级的变体。这一项尚未解决。

### 4. 绘制的量级不同，`N` 缩放则一致

两个面板不共用 y 轴：Fig. 3(a) 从 `65.6` 跨到 `78.8`，Fig. 4(a) 从 `86.5` 跨到 `103.2`。
因此按各自面板的刻度、而不是凭肉眼去读它们就很重要，而
`python scripts/measure_fig_levels.py` 正是做这个读取的：

| | Fig. 3(a), `N = 4` | Fig. 4(a), `N = 8` | ratio |
| --- | --- | --- | --- |
| Paper, Belief-DPP (oracle) | `66.74` | `87.89` | `1.32` |
| This replica, oracle (median) | `70.44` | `92.12` | `1.31` |
| This replica, oracle (mean) | `76.05` | `95.48` | `1.26` |

本复现的两行是 `results/penalty_tails.csv` 中的 oracle 条目。缩放是一致的；量级不是。
论文的 penalty 在 `N = 4` 与 `N = 8` 之间上升 `1.32`，本复现的（按中位数）上升
`1.31`——相差 `0.01`，比读数的那个面板 `2.0` 个单位的刻度间距还低一个数量级。剩下的是
一个量级偏移：对均值而言是 `N = 4` 时 `9.3` 个单位、`N = 8` 时 `7.6` 个单位，对中位数
而言是 `3.7` 和 `4.2`。

该与这两行中的哪一行比较，不是一个细节，因为论文所绘的量级本身是对未说明次数的运行取的
均值，而本复现自己的均值与中位数在 `N = 4` 时相差 `5.6` 个单位（se `1.1`）。造成这一
差距的可能原因是重尾，而不是建模错误。在 `theta ~ U[0,1]` 下，平均 event age
`E[(1 - theta) / theta]` 发散，因此跨运行的均值被少数 `theta` 极小的 arm 所主导。论文
说明了 `m = 50` 个 episode，但没有说明对 `theta*` 做了多少次独立抽样再取平均，因此这
两个均值并不是在以相同精度估计同一个有限量，而这一量级的偏移不能归因于本复现。

如果 penalty 在 `N = 4` 与 `N = 8` 之间翻倍，它会在 Fig. 4(a) 中落到 `133`，高于该面板
自身 `103.2` 的坐标轴上限。penalty 是 `sum_i gamma_i Y_i` 且 `sum_i gamma_i = 1`，因此它
是在各 arm 上取平均而不是跨 arm 累加，模型与论文自己的界中都没有任何东西把它按 `N` 缩放。

论文把 Fig. 3 和 Fig. 4 截断在第 50 个 episode，因为其合成运行是 `m = 50`。
`src/plot/draw.py` 绘制的正是这个 0..50 窗口。其背后的 CSV 保存了 100 个 episode ——
也就是 Fig. 6 和 Fig. 7 使用的长度 —— 因此移动窗口只需改 `HORIZON`，无需重新模拟。

### 5. "Time-averaged regret" 未被定义，因此两个纵坐标不是同一个量

Fig. 6 绘制的量被论文称作 time-averaged regret，却没有定义归一化方式，而且没有任何一种
归一化能同时适配 Fig. 5 和 Fig. 6。Fig. 5 显示在 `N = 3, L = 20` 时真实世界的逐 episode
penalty 大致在 60 到 200 之间——在其四个面板中，最低的第 1 个 episode 点值是 `63.2`，
最高的平台是 `190.3`（`python scripts/measure_fig_levels.py`）——因此一整个 episode 的
代价至多约 200。然而 Fig. 6 的起点高得多：在第 1 个 episode 处，它的五条曲线落在
`2264` 到 `3925` 之间，区间上端是定理给出的 upper bound，另外四条是 TS-DPP 在
`V = 0.5, 1, 5, 10` 下的曲线（`python scripts/measure_fig_levels.py`；该面板的图例把两条
不同的曲线都标成 `L = 20, V = 0.5`，所以那条虚线是依据论文正文把它与"the upper bound we
established"对举才认定为上界的）。若读作逐 episode regret，第 1 个 episode 就会是整个
episode 总 penalty 的 `11` 到 `20` 倍；若读作逐 slot 平均，则约为每 slot penalty `10` 的
`226` 到 `392` 倍。无论哪种读法，这个常数都不是 Fig. 5 所能支持的，而论文也没有说明它
是什么。

本复现绘制的是逐 episode 贝叶斯 regret 的滑动平均，

```
Delta_l          = E_{theta*}[ pen_l(policy) ] - E_{theta*}[ pen_l(oracle) ]
time-averaged(l) = (1/l) * sum_{j<=l} Delta_j
```

其中定理 2 的界被缩放到与第 1 个 episode 共用同一个锚点，因为论文的界带有一个未指定的
常数。只有衰减率的比较是有意义的，而它确实成立：经验曲线在第 100 个 episode 时降到
`0.53`，而界高出 `2.3x`（最宽处 `2.8x`）。出于同样的原因，四条 `V` 曲线在这里重合：
regret 由估计误差主导，而 `V` 对端点的影响不到 6%（`V = 0.5` 时为 `0.535`，`V = 1` 时为
`0.563`）。它们在论文里却*不*重合，这不过是同一个含糊之处从另一面显形：论文的四条
TS-DPP 曲线起点落在 `2264` 到 `3578` 之间，平台落在 `19` 到 `116` 之间，相差六倍，而该图
的正文却把这四条都描述为收敛。若论文的 regret 是相对于 `V` 最优策略而非本复现的 oracle
来度量，`V` 就会像那些面板显示的那样改变量级。论文没有说明用的是哪个参照，所以这里的
重合并不构成对论文的反证——但它确实意味着两张图画的不是同一个量，而本差异讲的正是这件
事。

### 6. Fig. 5 的 trace 切片是从论文自己的计数反推出来的

论文明确指派了这两种设定，因此哪张图用哪个数据集无需猜测："In the synthetic experiments, we
display the episodic penalty trends ... as illustrated in Fig. 3 and Fig. 4"，以及 "we
evaluate its performance on a real-world dataset under varying values of the hyperparameter
`V ∈ {0.04, 0.06, 0.08, 0.10}`. As illustrated in Fig. 5"。Fig. 3、Fig. 4 与 Fig. 6 用合成
设定；Fig. 5 用 trace。

参考文献 [31] 只给出 Kaggle URL，别的什么都没有——没有月份、没有文件名、没有版本。下载
本身不是障碍；它不需要账号：

```
curl -L -o cosmetics.zip \
  "https://www.kaggle.com/api/v1/datasets/download/mkechinov/ecommerce-events-history-in-cosmetics-shop"
unzip -d cosmetics cosmetics.zip                        # five monthly CSVs, 2019-Oct to 2020-Feb
python src/sim/extract.py cosmetics/2019-Dec.csv.gz     # -> data/2019-Dec-3types.npz
```

论文说它排除了 "one type of infrequent event"，保留其余三种，并计得 1,654,771 次发生。
这个数是*被占用的 1 秒时隙*数，而不是行数：论文把每个时间戳映射到一个统一的 1 秒时隙，
并把该时隙当作事件的实际发生时刻，因此落在同一秒内的事件会合并为一个。在每一个按月文件
上、对其四种事件类型的每一个二、三、四类型子集，分别统计行数、被占用时隙数、去重用户数
和去重 `(user, item)` 对，只有一个切片落在 0.5% 以内：

| 切片 | 计数 | 偏差 | 相对 |
| --- | --- | --- | --- |
| 2019-Dec `view` + `cart` + `remove_from_cart`，被占用时隙 | 1,647,519 | −7,252 | −0.44% |
| 2019-Oct `view` + `cart` + `purchase`，被占用时隙 | 1,645,164 | −9,607 | −0.58% |
| 2020-Jan `view` + `purchase`，去重 `(user, item)` | 1,662,767 | +7,996 | +0.48% |
| 2019-Dec `cart` + `remove_from_cart` + `purchase`，行数 | 1,804,955 | +150,184 | +9.1% |

第一行才是描述所指向的那一个。`purchase` 就是不频繁的那一类——12 月里只占 29,137 个
非空秒，而其余三类每一个都在 422,184 以上——并且 12 月是唯一一个其三类的量小到够用的
月份；另外四个月都给出 1,717,728 或更多。残留的 0.44% 最可能是快照版本不同：当前数据集
中全部五个文件的日期都是 2020-03-16，而 Kaggle 数据集可以被原地替换。

该表中只有第一行可以从本仓库核对：`data/2019-Dec-3types.npz` 正好带着那三种类型，读者
可以重新数它的被占用时隙。其余三行——`purchase` 的 `29,137`、其余月份的 `1,717,728`、
以及文件日期——需要原始的按月 CSV，而它们并未提交到本仓库。这些数只依据一次读取，因此
在此按“一次读取”标注，而不是当作可复现的结果呈现。

`theta` 来自 trace，也只来自 trace——`view` 0.4391、`cart` 0.2702、`remove_from_cart`
0.1576 个被占用时隙/秒。`gamma`、`c` 和 `B` 沿用第 V-A-1 节声明适用于 "all simulations"
的那套配置（Dirichlet 且 `sum gamma = 1`、`U[0.2, 0.5]`、`0.35`）。事件是从 trace 中回放
的，而不是从 `Bernoulli(theta_hat)` 重采样：Bernoulli 那句只写给了合成设定，而且拟合一个
速率会把 burstiness 丢掉，而那正是使用真实 trace 的全部理由。回放也比重采样更接近论文的
量级。论文没有说明 Fig. 5 对多少次运行取平均；它只在 Fig. 6 处给出过一次 Monte Carlo
sample size 为 1000，本复现对 Fig. 5 也用 1000 次，每次运行重新抽取 instance，并在同一次
抽取上模拟全部四个 `V`，从而让四个面板保持配对。

**episode 边界同时决定了 Fig. 5 的形状和量级。** 论文没有说明 AoI 状态 `X, Y` 是否跨越
episode 边界存活，而这是唯一一个能把一条平线变成论文那条曲线的选择。同一份 trace、同一个
`theta_hat`、其余一切相同。各行取的是 oracle —— 它已知 `theta*`、不学习，因此除了预热之外
没有别的因素在动：

| `X, Y` 在 episode 边界处 | 第 1 个 episode | 第 5 个 | 平台 | ep1 / plateau |
| --- | --- | --- | --- | --- |
| 重置为 0 | 96.9 | 98.2 | 98.7 | 0.981 |
| 跨集延续 | 96.9 | 151.1 | 154.6 | 0.627 |
| 论文, Fig. 5(b), TS-DPP | `63.2` | `124.5` | `145.9` | `0.43` |
| 论文, Fig. 5(b), Lyapunov | `69.9` | `133.3` | `155.5` | `0.45` |
| 论文, Fig. 5(b), Whittle | `83.0` | `150.1` | `173.2` | `0.48` |

表内各行是 `V = 0.06`，即论文的 Fig. 5(b)，来自 `python src/diagnose.py carry`，它会打印
每一个 `V`。前两行是 oracle，而论文的 Fig. 5 并未绘制它：它放在这里是为了隔离预热，因为它
已知 `theta*`、不学习。后三行是论文自己的那三条曲线，由
`python scripts/measure_fig_levels.py` 按其光栅刻度读出。

virtual queue 不在这项选择之内。式 (7) 对长度为 `L` 的单个 episode 取成本平均，因此两行里
`Z` 都在每个 episode 开头被清零。连 `Z` 一起延续反而会发散：约束永不停止生效，`Z` 无界增长，
在 `V = 0.06` 处到第 100 个 episode 时 penalty 达到 `321` 并且还在上升。完全没有 `Z` 的 Whittle 是唯一在
延续 `Z` 时仍保持有界的 policy。`simulate` 带一个 `carry` 开关，它只延续 `X, Y`。

延续 `X, Y` 同时也抹平了量级差，而且用的就是 12 月切片自己的
`theta_hat = (0.4391, 0.2702, 0.1576)` —— 事件率不需要任何修正。在 `V = 0.06` 处按同一条
policy 与论文自己的曲线相比，平台是对得上的：Lyapunov `154.4` 对 `155.5`，TS-DPP `155.4`
对 `145.9`，Whittle `188.0` 对 `173.2`（`results/realworld_curves.csv`）。重置时 oracle
的平台是 99，而这个缺口全部来自逐 episode 的预热，与数据无关。

**同一个开关会修好 Fig. 3 与 Fig. 4 的排序，却会破坏它们的形状。** 在 `carry` 下合成曲线
同样上升，`N = 4, L = 20, V = 0.2` 时 oracle 的 `ep1 / 平台` 为 0.57、TS-DPP 也是 0.57，
而论文的那两条是下降的。在 `reset` 下这两张图是对的，Fig. 5 又不对。没有任何单一设定能同时
产出两者，因此本复现对 trace 延续、对合成曲线重置：合成设定每次运行都重新抽取 `theta*`，
所以一个 episode 就是一次独立实验；而 trace 里面根本没有边界。Whittle 的排序也随同一个开关
翻转——`reset` 下最低、`carry` 下最高——因此差异 1 至少有一部分来自这一选择，而不是 policy
结构本身的差别。

**还剩两处残留。** 一是第 1 个 episode 的深度：本复现的 TS-DPP 从平台的 `0.67` 起步，论文
的是 `0.43`；Lyapunov 是 `0.65` 对 `0.45`。恢复也更快——到第 5 个 episode 时，本复现的
TS-DPP 和 Lyapunov 分别为各自平台的 `1.02` 和 `0.98`，论文的是 `0.85` 和 `0.86`。两者都
取决于一个 20 slot 的 episode 需要重建多少 age，而这取决于窗口落在 trace 的哪一段，论文
没有说明它如何选取窗口。另一处是上面切片表里的 0.44% 计数缺口。

这里的排序与论文一致，四个面板中 Whittle 都最高，与 Fig. 3、Fig. 4 不同。差异 1 只适用于
那两张。

### 7. 预算约束只咬住那些遵守它的 policy

论文把 `B` 设为均匀随机选择 arm 的期望 cost，而 `c_i ~ U[0.2, 0.5]` 的均匀抽取给出的恰好
是 `0.35`。因此任何对价格无所谓的 policy 都自动满足该约束。约束真正做的事，是把那些
*确实* 带有 virtual queue 的 policy 推向比它们原本会花的更少的开销。

在每条 policy 相同的 200 个 instance 上汇总（`python src/diagnose.py cost`），实际 cost
分得很干净：

| Policy | Realised cost | se | `(mean − B) / se` |
| --- | --- | --- | --- |
| Belief-DPP (oracle) | `0.3467` | `0.0036` | `-0.9` |
| TS-DPP | `0.3469` | `0.0036` | `-0.9` |
| Lyapunov [20] | `0.3471` | `0.0036` | `-0.8` |
| Whittle [24], no queue | `0.3514` | `0.0035` | `+0.4` |

Whittle 因为 [24] 未规定预算控制而不带 queue，它正好落在 `B` 上，t 统计量为 `+0.4`
——它没有超支，而把它与其余策略区分开的也不是约束。行为反常的是那三条带 queue 的 policy：
它们的 queue 把它们压到预算 *之下* 0.8% 到 0.9%。在相同的 instance 上配对比较
（`results/cost_paired.csv`），Whittle 比 TS-DPP 多花 `0.0045`（se `0.0012`，t `3.8`），
比 Lyapunov 多 `0.0044`，比 oracle 多 `0.0048`（se `0.0013`，t `3.7`）。

所以该约束与其说是松弛的，不如说是单边的：它让 DPP 各 policy 付出 penalty 代价，而对一个
不带 queue 的 policy 则分文不取。这是差异 1 的后半部分——把 queue 还给 Whittle 会把它的
cost 从 `0.3514` 降到 `0.3485`，并让它 `-2.84` 的 penalty 优势中的 `-2.74` 依然成立。

### 8. Fig. 7 的阴影带不是 95% 区间

论文说 Fig. 7 的阴影区域 "indicate the 95% confidence intervals of the beta distribution"，
而本复现绘制的正是这些：式 (14) 所维护的 `Beta(alpha, beta)` 的 2.5 与 97.5 百分位，取自
绘制该图所用的同一个 `model.posterior_path` 调用。点估计的表现与正文描述一致——它们从
先验附近出发，最终稳定在 `theta*` 附近。覆盖率则不然。`python src/diagnose.py fig7` 运行
300 次实现，并统计阴影带包含 `theta*` 的频率：

| episodes | `theta* = 0.239` | `0.489` | `0.839` |
| --- | --- | --- | --- |
| 20 | 86.3% | 91.7% | 94.0% |
| 50 | 74.3% | 84.3% | 92.0% |
| 100 | 65.7% | 77.7% | 81.0% |

覆盖率随 episode 累积而下降。在同一区间内，阴影带的平均宽度在三个 `theta*` 处各收窄
`28` 到 `34` 个百分点，而在 `0.239` 和 `0.839` 处 RMSE 只下降 `4.5` 和 `6.1` 个百分点
——在那里，区间围绕一个并没有在改善的估计收紧了。在 `0.489` 处 RMSE 的下降超过阴影带的
下降，`46` 对 `34` 个百分点，而覆盖率仍然掉了 `14` 个点，这指向的是估计而不是阴影带。

图自身的实现就展示了这一点。在面板 (b) 中，从第一个检查点起阴影带就完全位于真值 *之上*：
`ci_low` 在第 20 个 episode 处是 `0.5117`，在第 100 个 episode 处是 `0.5095`，而
`theta* = 0.489`（`results/estimates.csv`，即 `figs/fig7.png` 背后的数据）。对照那条红线
检查该面板的读者，看到的是一个错失的区间，而不只是一个偏窄的区间。

估计还始终偏向中间：小的 `theta*` 被高估、大的 `theta*` 被低估，在第 100 个 episode 处
分别是 `+0.045`、`+0.012` 和 `-0.025`，每个都在 4 到 10 个标准误之间。该偏差不衰减。把
policy 移除、换用轮询式拉动，使只有式 (14) 处于被检验状态时，它在 6,400 次拉动后于
`theta = 0.239` 处仍是 `+0.0397`（se `0.0006`），在 25,600 次后是 `+0.0396`（se
`0.0002`）——在样本量翻两番的过程中保持平坦，`bias x pulls` 在该区间内从 `253.8` 升到
`1014.3`，而不是趋于平稳。另外两个 `theta` 表现相同（`python src/diagnose.py eq14`）。

产生它的不是式 (14)。当某个 arm 的每次拉动都恰好在上一次之后的 `g` 个 slot 时，该更新是
无偏的：其 `alpha` 的每次拉动期望为 `1 - (1 - theta)^g`，`beta` 的为
`sum_{s<g} (1 + s) theta (1 - theta)^s + g (1 - theta)^g`，两者的比值在每一个尝试过的
`g` 和 `theta` 处都在 `3e-17` 以内等于 `theta`（`python src/diagnose.py eq14`）。

偏差存在于 episode 边界处。`simulate` 在每个边界处把时钟 `t_prev` 和先前的 age `s_prev`
重新清零，因此每个 arm 在每个 episode 中的第一次拉动，是对着被边界刚刚截断的历史来计分
的。当 age 也被重置时，观测到的 age 至多为 `t - 1`，而 `n_gap` 是 `t`，于是式 (14) 被
*强制*为 `I = 1`：在几乎没有失败记录的情况下记入一次成功。改为延续 age 则把真实的延续
age 交给式 (14)，它通常超过被截断的时钟，于是式 (14) 记入 `I = 0`，并把整个延续 age 当作
一串失败计入 `beta`。这正是测得偏差移动的方向，在 `theta = 0.239` 处从 `+0.042` 到
`-0.023`；在 100 个 episode、一个 seed 下，`reset` 让第一个 arm 的 `alpha` 多记 `56`、
`beta` 少记 `211`，在 20 个 seed 上平均为 `59` 和 `238`。

论文没有说明它的 Fig. 7 用哪种约定，而两种都是有偏的——`reset` 抬高估计，`carry` 压低
估计——因此上面的覆盖率表不是选错了约定的产物。表中的数字是 `reset` 约定，也就是
`posterior_path` 绘制该图所用的约定。

那些被伪造的成功以固定的速率到来——每个 arm 每个 episode 一次，即每 `L` 次拉动中有 `N`
次——这就是偏差不随数据增多而衰减的原因。episode 边界每次都会重新伪造同一个单边读数，
因此污染是样本中一个恒定的 *比例*，而不是一个趋于消失的量；增加 episode 是以相同的比例
加入有偏与无偏的拉动。

## 问题

如有 bug、疑问或讨论，请使用本仓库的 issues 区。

## 贡献

我们欢迎有助于提升复现准确性的贡献。Fork 本仓库，提交你的改动，并发出 pull request。
