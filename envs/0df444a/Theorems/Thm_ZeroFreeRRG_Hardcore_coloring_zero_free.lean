-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_zero_free
-- name    : ZeroFreeRRG.Hardcore.coloring_zero_free
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T04:59:01.436392+00:00
-- url     : https://prove2.me/theorems/e06e4d05-abbe-449a-b1f5-4ca7192362e9
-- title:
--   Zero-free region including the coloring endpoint
-- statement:
--   Fix integers $d,q\ge3$ with $d<d_{\rm RSB}(q)$. There exists $\eta>0$ such that, with probability $1-o_n(1)$ over a uniformly random simple $d$-regular graph $G$, the Potts partition function is zero-free throughout
--
--   $$D([0,1],\eta),$$
--
--   including the proper-coloring point $\beta=0$. The limit is along admissible values of $n$. This is the coloring branch of Theorem 1.4.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Theorem 1.4(2), printed p. 5, and proof §5.4, printed p. 40.

import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsThresholds
open scoped Classical

namespace ZeroFreeRRG.Hardcore
/-- The proper-coloring endpoint branch of Theorem 1.4. -/
theorem coloring_zero_free (d q : ℕ) (hd : 3 ≤ d) (hq : 3 ≤ q)
    (h : (d : EReal) < coloringDegreeRSB q) :
    ∃ η : ℝ, 0 < η ∧ PottsRapidMixing.WithHighProb d (fun n G =>
      ∀ β ∈ nbhd (realSegment 0 1) η, pottsZ q G β ≠ 0) := by sorry
end ZeroFreeRRG.Hardcore
