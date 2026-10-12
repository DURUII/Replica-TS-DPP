# 脚本

[English](README.md) | 中文

这里的每个脚本都属于三类之一，而类别就是它做出的承诺。

| 文件 | 类别 | 是什么 |
|------|------|--------|
| `verify_translation_pairing.py` | 门禁 | 双语 README 配对漂移时让构建失败，依据 `translation-pairing.manifest.json` |
| `verify_doc_budgets.py` | 门禁 | 常驻文档超出字数上限时让构建失败，依据 `doc_budgets.manifest.json` |
| `measure_fig_levels.py` | 校验 | 从论文自己的图里栅格化出各条曲线，记录复现实验所对照的电平 |
| `numeric_check.py` | 校验 | 论文解析结论的数值证伪器；通过意味着 N 次试验内没找到反例，而不是证明 |
| `recon_l5_*.py` | 探针 | 找出 Lemma 5 反例的那段探索。既不是证明，也不是门禁 |

## 探针层

`recon_l5_sweep.py` 是产出 `recon_l5_sweep.json` 的那次扫描，560 行，同一个不等式在一组形状
与半径上逐点求值。其余的是通往那里的工具。`recon_l5_mp.py` 与 `recon_l5_fast.py` 在对数空间
以 60 位精度求双样本概率，用于双精度密度下溢的形状。`recon_l5_crosscheck.py` 用结构不同的
归约算同一个数，因此一条路线上的错误不会传到另一条。`recon_l5_mc.py` 与
`recon_l5_mcvalidate.py` 用蒙特卡洛确认其中一个子集。`recon_l5_boundary.py` 定位界在哪里
首次失效，并复检论文自己声明的范围。

保留它们，是因为它们是反例如何被找到的记录，也因为 `DESIGN.md` 与 `cards/L5-REFUTATION.md`
里引用的数字就是从它们读出来的。它们不被维护，不是门禁，成果物也不依赖它们再跑一次。同一个
结果的机器校验形式是 `lean4/TSDPP/Lemma5Refutation.lean`，它与这些脚本不共享任何代码，也不
依赖其中任何一个文件。

## 运行

```
python scripts/verify_translation_pairing.py
python scripts/verify_doc_budgets.py
python scripts/numeric_check.py
python scripts/measure_fig_levels.py --pdf /path/to/camera-ready.pdf
```

`measure_fig_levels.py` 需要论文的 camera-ready PDF，本仓库不分发它。用 `--pdf` 传入，或设置
`PAPER_PDF`。
