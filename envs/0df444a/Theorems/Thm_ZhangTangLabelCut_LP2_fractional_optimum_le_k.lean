-- Prove2me | Theorems.Thm_ZhangTangLabelCut_LP2_fractional_optimum_le_k
-- name    : ZhangTangLabelCut.LP2.fractional_optimum_le_k
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T05:14:31.227985+00:00
-- url     : https://prove2.me/theorems/32b61c59-01e8-4e95-b6bb-8c736f634473
-- title:
--   Lemma 5.2 — every realization has fractional optimum at most k
-- statement:
--   Let $k\ge2$, $d,h>0$ be integers. For every realization $I$ of the Section 4 shutter construction, in either orientation, the actual fractional optimum of the distinct-label relaxation satisfies
--   $$\operatorname{OPT}_f(\mathrm{LP2}(I))\le k.$$
--   All real nonnegative feasible label weights are allowed. The assertion holds for every permutation sample, not only a sample with a large integral cut.
--
--   Differences from the source:
--   - encoding: one-based finite label and chain indices → zero-based Fin indices; reason: reindexing preserves every instance and cardinality
--   - encoding: Section 4 integer construction parameters → explicit k ≥ 2, d > 0 and h > 0; reason: these specify the source construction regime
--   - encoding: undirected construction, with the directed extension in Section 7 → a Boolean orientation quantified over both cases; reason: both source graph orientations are preserved
--   - encoding: the LP optimum → the real part of its extended-real infimum; reason: this concrete LP is feasible, nonnegative and has an attained finite optimum; no infinite default is used
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), p. 13, Lemma 5.2; p. 23, Section 7

import Definitions.Def_ZhangTangLabelCut_LP2_FiniteGraph
import Definitions.Def_ZhangTangLabelCut_LP2_CoveringLP
import Definitions.Def_ZhangTangLabelCut_LP2_LabelCut
import Definitions.Def_ZhangTangLabelCut_LP2_Shutter
import Definitions.Def_ZhangTangLabelCut_LP2_Configurations

namespace ZhangTangLabelCut.LP2

theorem fractional_optimum_le_k (k d h : ℕ) (hk : 2 ≤ k) (hd : 0 < d) (hh : 0 < h)
    (directed : Bool) (σ : Sample k d h) :
    (shutterInstance k d h directed σ).frac ≤ (k : ℝ) := by sorry

end ZhangTangLabelCut.LP2
