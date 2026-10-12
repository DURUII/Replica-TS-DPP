# Scripts

English | [中文](README.zh.md)

Every script here is one of three kinds, and the kind is the promise it makes.

| file | kind | what it is |
|------|------|------------|
| `verify_translation_pairing.py` | gate | fails the build when a bilingual README pair drifts, against `translation-pairing.manifest.json` |
| `verify_doc_budgets.py` | gate | fails the build when a standing doc exceeds its word ceiling, against `doc_budgets.manifest.json` |
| `measure_fig_levels.py` | check | rasterises the paper's own panels and records the levels the replica is compared against |
| `numeric_check.py` | check | the numeric falsifier for the paper's analytic claims; a pass means no counterexample in N trials, not a proof |
| `recon_l5_*.py` | probe | the exploration that found the Lemma 5 counterexamples. Neither a proof nor a gate |

## The probe tier

`recon_l5_sweep.py` is the sweep that produced `recon_l5_sweep.json`, 560 rows of the same
inequality evaluated across a grid of shapes and radii. The rest are the tools that got there.
`recon_l5_mp.py` and `recon_l5_fast.py` evaluate the two-sample probability in log space at 60
digits, for shapes where the double-precision density underflows. `recon_l5_crosscheck.py`
computes the same number by a structurally different reduction, so an error in one route does not
propagate into the other. `recon_l5_mc.py` and `recon_l5_mcvalidate.py` confirm a subset by Monte
Carlo. `recon_l5_boundary.py` locates where the bound first fails and re-checks the paper's own
range.

They are kept because they are the record of how the counterexample was found, and because the
numbers quoted in `DESIGN.md` and `cards/L5-REFUTATION.md` were read off them. They are not
maintained, they are not a gate, and nothing in the artifact depends on running them again. The
machine-checked form of the same result is `lean4/TSDPP/Lemma5Refutation.lean`, which shares no
code with them and does not depend on any of these files.

## Running

```
python scripts/verify_translation_pairing.py
python scripts/verify_doc_budgets.py
python scripts/numeric_check.py
python scripts/measure_fig_levels.py --pdf /path/to/camera-ready.pdf
```

`measure_fig_levels.py` needs the paper's camera-ready PDF, which this repository does not
distribute. Pass it with `--pdf` or set `PAPER_PDF`.
