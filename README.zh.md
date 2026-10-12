# Replica-TS-DPP：理论复核与实验复现

[English](README.md) | 中文

## 概述

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

[原论文](https://doi.org/10.1109/INFOCOM59046.2026.11571737)研究不确定事件捕获问题，将其表述为转移概率未知的受约束 episodic restless bandit 模型。

为求解这一问题，论文提出 *TS-DPP* 算法，将基于信念的漂移+惩罚策略与 Thompson 采样相结合。

本项目工作有二：审查论文的理论论证，复现论文的实验结果。由此发现两个主要问题：

1. 理论方面：论文引理 5 使用和证明错误。一个简单反例表明，这一步所用的界不成立。见[问题分析与反例](FINDING.md)。
2. 实验方面：在采用 episode 重置实现中，Whittle 的每 episode 罚值低于 oracle，与论文报告的排序相悖。见[实验结果与差异分析](code/README.md#differences-from-the-paper)。

## 复现结果

| 来源 | 图 3（`N = 4`） | Whittle 罚值相对 oracle |
| --- | --- | --- |
| [原论文](https://doi.org/10.1109/INFOCOM59046.2026.11571737) | ![原图 3](docs/assets/paper-fig3.png) | 更高 |
| 本项目复现 | ![复现图 3](code/figs/fig3.png) | 更低 |

复现图依据[模拟数据](code/results/penalty_curves.csv)绘制。[原图测读数据](code/results/paper_levels.csv)与[实现选择](code/README.md#difference-1)给出比较依据。

图 4：`N = 8` 时各 policy 的 episode 罚值。

![复现图 4](code/figs/fig4.png)

图 5：真实 trace 回放结果。

![复现图 5](code/figs/fig5.png)

图 6：相对 oracle 的累计 episode regret 平均值。

![复现图 6](code/figs/fig6.png)

图 7：posterior 均值与 Beta 95% 可信区间。

![复现图 7](code/figs/fig7.png)

八项差异及解释见 [Code README](code/README.md#differences-from-the-paper)。

## 阅读指南

| 内容 | 从哪里开始 |
| --- | --- |
| 理论论证与形式化验证 | [cards/](cards/README.md) 列出定理、证明与反证，并说明证明路线及各项结论的依赖关系；[lean4/](lean4/) 提供相应的形式化实现 |
| 实验与复现 | [code/](code/README.md) 给出模拟程序、CSV 数据、图表及差异分析 |
| 数值探索与审计工具 | [scripts/](scripts/README.md) 包含数值探索及仓库检查脚本；[lean4/scripts/](lean4/scripts/) 提供构建与公理审计工具 |
| 推导过程及其与论文的对应关系 | [DESIGN.md](DESIGN.md) 记录推导过程；[FIDELITY.md](FIDELITY.md) 审查形式化陈述与论文对应关系 |

## 致谢

[CLAUDE.md](CLAUDE.md) 中的证明工作方法，受陶哲轩谈论 Lean 辅助数学研究的采访启发。

相关讨论可参阅他接受 [Scientific American 的采访](https://www.scientificamerican.com/article/ai-will-become-mathematicians-co-pilot/)，其中谈到证明分解，并记录失败的尝试；以及他[与 Lex Fridman 的对谈](https://lexfridman.com/terence-tao-transcript/)，其中谈到 Lean blueprint 与证明依赖图。
