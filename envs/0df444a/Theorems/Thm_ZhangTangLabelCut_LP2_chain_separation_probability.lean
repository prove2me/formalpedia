-- Prove2me | Theorems.Thm_ZhangTangLabelCut_LP2_chain_separation_probability
-- name    : ZhangTangLabelCut.LP2.chain_separation_probability
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:14:17.322983+00:00
-- url     : https://prove2.me/theorems/c3d1488b-ba9d-47be-a88f-0c1d81c7dab4
-- title:
--   Lemma 6.1 — separation probability for one chain
-- statement:
--   Let $k\ge2$ and $d,h>0$ be integers in the shutter construction, in either orientation. Fix a nonempty candidate label set $S$, put $a=|S|/k$, and suppose $d>8a$. Choose a chain $C^i_{\mu\nu}$ whose two ground elements are light for $S$, meaning $|J_\mu|,|J_\nu|\le4a$. Under independent uniform permutations,
--   $$\mathbb P[S\text{ separates }s,t\text{ in }C^i_{\mu\nu}]\le1-(1-8a/d)^{4a}.$$
--   This is the single-chain probability bound.
--
--   Differences from the source:
--   - encoding: one-based finite label and chain indices → zero-based Fin indices; reason: reindexing preserves every instance and cardinality
--   - encoding: Section 4 and Section 6 standing positive integer parameters and d > 8a → the same positive regime, enforced by hypotheses and inhabited chain indices, with d > 8a; reason: these are the source construction regime and p. 17 condition; redundant positivity binders are omitted, and 4a stays real
--   - encoding: undirected construction, with the directed extension in Section 7 → a Boolean orientation quantified over both cases; reason: both source graph orientations are preserved
--   - encoding: independent uniform permutations → finite counting probability on the full product of permutation groups; reason: the sample space has cardinality (d!) to the number of chains
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), p. 16, Lemma 6.1; p. 17, standing d > 8a; p. 23, Section 7

import Definitions.Def_ZhangTangLabelCut_LP2_FiniteGraph
import Definitions.Def_ZhangTangLabelCut_LP2_CoveringLP
import Definitions.Def_ZhangTangLabelCut_LP2_LabelCut
import Definitions.Def_ZhangTangLabelCut_LP2_Shutter
import Definitions.Def_ZhangTangLabelCut_LP2_Configurations

namespace ZhangTangLabelCut.LP2

theorem chain_separation_probability (k d h : ℕ)
    (directed : Bool) (S : Finset (Fin k × Fin d)) (hc : 0 < S.card)
    (hreg : 8 * average k S.card < (d : ℝ)) (c : Chain k h)
    (hμ : c.1.val.1 ∈ light S) (hν : c.1.val.2 ∈ light S) :
    probability k d h (chainSeparated directed S c) ≤ chainBound (average k S.card) d := by sorry

end ZhangTangLabelCut.LP2
