-- Prove2me | Theorems.Thm_ZhangTangLabelCut_LP2_configuration_probability
-- name    : ZhangTangLabelCut.LP2.configuration_probability
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:14:41.538236+00:00
-- url     : https://prove2.me/theorems/5d43198f-3676-4614-b3b7-700d82b8511c
-- title:
--   Lemma 6.2 — probability of a good configuration
-- statement:
--   Let $k\ge2$ and $d,h>0$ be integers in the shutter construction, in either orientation. Fix a nonempty label subset $S$, set $a=|S|/k$, and assume $d>8a$. Let $\Phi'(S)$ be its light ground set and $F(S)$ its configuration. For independent uniform permutations,
--   $$\mathbb P[F(S)\text{ disconnects the union of shutters on }\Phi'(S)]\le[1-(1-8a/d)^{4a}]^{(h/2)(3k/4)(3k/4-1)}.$$
--   The originating $S$ is fixed before the random draw. This is the configuration probability bound.
--
--   Differences from the source:
--   - encoding: one-based finite label and chain indices → zero-based Fin indices; reason: reindexing preserves every instance and cardinality
--   - encoding: Section 4 and Section 6 standing positive integer parameters and d > 8a → the same positive regime, enforced by hypotheses and inhabited chain indices, with d > 8a; reason: these are the source construction regime and p. 17 condition; redundant positivity binders are omitted, and 4a stays real
--   - encoding: undirected construction, with the directed extension in Section 7 → a Boolean orientation quantified over both cases; reason: both source graph orientations are preserved
--   - encoding: independent uniform permutations → finite counting probability on the full product of permutation groups; reason: the sample space has cardinality (d!) to the number of chains
--   - encoding: F and its associated light ground set from L′ → the event is indexed by the original fixed candidate S; reason: keeps zero-count light elements and does not assume that F alone determines its light ground set
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), p. 18, Lemma 6.2; pp. 14–17, standing setup; p. 23, Section 7

import Definitions.Def_ZhangTangLabelCut_LP2_FiniteGraph
import Definitions.Def_ZhangTangLabelCut_LP2_CoveringLP
import Definitions.Def_ZhangTangLabelCut_LP2_LabelCut
import Definitions.Def_ZhangTangLabelCut_LP2_Shutter
import Definitions.Def_ZhangTangLabelCut_LP2_Configurations

namespace ZhangTangLabelCut.LP2

theorem configuration_probability (k d h : ℕ) (hk : 2 ≤ k) (hh : 0 < h)
    (directed : Bool) (S : Finset (Fin k × Fin d)) (hc : 0 < S.card)
    (hreg : 8 * average k S.card < (d : ℝ)) :
    probability k d h (good directed S) ≤ configurationBound k h (average k S.card) d := by sorry

end ZhangTangLabelCut.LP2
