-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_positive_zero_free
-- name    : ZeroFreeRRG.Hardcore.potts_positive_zero_free
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T04:56:28.817602+00:00
-- url     : https://prove2.me/theorems/a29c7231-1e57-4b8f-8feb-cc35aaedda3d
-- title:
--   Positive-temperature Potts zero-free region
-- statement:
--   Fix $d\ge3$, $q\ge2$, and $0<\delta<1-\beta_{\rm RSB}(d,q)$. There exists $\eta>0$ such that, with probability $1-o_n(1)$ over a uniformly random simple $d$-regular graph $G$, the Potts partition function is zero-free throughout
--
--   $$D\!\left([\beta_{\rm RSB}(d,q)+\delta,1],\eta\right).$$
--
--   The limit is along admissible $n$ with $nd$ even. This is the positive-temperature branch of Theorem 1.4.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Theorem 1.4(1), printed p. 5; proof §5.4, printed p. 40.

import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsThresholds
open scoped Classical

namespace ZeroFreeRRG.Hardcore
/-- The positive-temperature Potts part of Theorem 1.4. -/
theorem potts_positive_zero_free (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) (δ : ℝ)
    (hδ : 0 < δ) (hδmax : δ < 1 - betaRSB d q) :
    ∃ η : ℝ, 0 < η ∧
      PottsRapidMixing.WithHighProb d (fun n G =>
        ∀ β ∈ nbhd (realSegment (betaRSB d q + δ) 1) η, pottsZ q G β ≠ 0) := by sorry
end ZeroFreeRRG.Hardcore
