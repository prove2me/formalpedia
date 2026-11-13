-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_corollary_1_6
-- name    : ZeroFreeRRG.Hardcore.corollary_1_6
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T04:44:12.757351+00:00
-- url     : https://prove2.me/theorems/59f57643-c010-4ca6-aac7-33e4c8464501
-- title:
--   Zero-free region for random regular antiferromagnetic Ising
-- statement:
--   Fix $d\ge3$ and $0<\delta<2/(\sqrt{d-1}+1)$. There is an $\eta>0$ such that, for a uniformly random simple $d$-regular graph $G$ on $n$ vertices,
--
--   $$\Pr\!\left[Z_{G,2}(\beta)\ne0\text{ for every }\beta\in D\!\left(\left[\frac{\sqrt{d-1}-1}{\sqrt{d-1}+1}+\delta,1\right],\eta\right)\right]\longrightarrow1.$$
--
--   The limit is along admissible $n$ with $nd$ even. This is the paper's Ising zero-freeness corollary, obtained from its Potts result and the explicit Ising replica-symmetry threshold.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Corollary 1.6, printed p. 6 (PDF p. 7).

import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
open scoped Classical

namespace ZeroFreeRRG.Hardcore

/-- Corollary 1.6: the antiferromagnetic Ising zero-free region. -/
theorem corollary_1_6 (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ)
    (hδmax : δ < 2 / (Real.sqrt ((d : ℝ) - 1) + 1)) :
    ∃ η : ℝ, 0 < η ∧
      PottsRapidMixing.WithHighProb d (fun n G =>
        ∀ β ∈ nbhd (realSegment
          ((Real.sqrt ((d : ℝ) - 1) - 1) / (Real.sqrt ((d : ℝ) - 1) + 1) + δ) 1) η,
          pottsZ 2 G β ≠ 0) := by sorry

end ZeroFreeRRG.Hardcore
