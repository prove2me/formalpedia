-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_theorem_1_4
-- name    : ZeroFreeRRG.Hardcore.theorem_1_4
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T04:54:01.236814+00:00
-- url     : https://prove2.me/theorems/68eb9b3d-7b4b-4852-b55e-6d769380251f
-- title:
--   Zero-free Potts and coloring regions up to the RSB thresholds
-- statement:
--   Fix integers $d\ge3$ and $q\ge2$. Let $G$ be a uniformly random simple $d$-regular graph on $n$ vertices, with $n\to\infty$ along values for which $nd$ is even.
--
--   1. For each $0<\delta<1-\beta_{\mathrm{RSB}}(d,q)$ there is $\eta>0$ such that, with probability $1-o_n(1)$, the Potts partition function $Z_{G,q}$ is zero-free throughout
--      $$D\!\left([\beta_{\mathrm{RSB}}(d,q)+\delta,1],\eta\right).$$
--   2. If $q\ge3$ and $d<d_{\mathrm{RSB}}(q)$, there is $\eta>0$ such that, with probability $1-o_n(1)$, $Z_{G,q}$ is zero-free throughout $D([0,1],\eta)$, including the proper-coloring endpoint $\beta=0$.
--
--   The thresholds are the Bethe positive-witness boundaries defined in equations (32) and (34).
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Theorem 1.4, printed p. 5 (PDF p. 6); thresholds in (32) and (34).

import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Definitions.Def_ZeroFreeRRG_Hardcore_PottsThresholds
open scoped Classical

namespace ZeroFreeRRG.Hardcore

/-- Theorem 1.4: zero-free Potts and coloring regions below the RSB thresholds. -/
theorem theorem_1_4 (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) :
    (∀ δ : ℝ, 0 < δ → δ < 1 - betaRSB d q →
      ∃ η : ℝ, 0 < η ∧
        PottsRapidMixing.WithHighProb d (fun n G =>
          ∀ β ∈ nbhd (realSegment (betaRSB d q + δ) 1) η, pottsZ q G β ≠ 0)) ∧
    (3 ≤ q → (d : EReal) < coloringDegreeRSB q →
      ∃ η : ℝ, 0 < η ∧
        PottsRapidMixing.WithHighProb d (fun n G =>
          ∀ β ∈ nbhd (realSegment 0 1) η, pottsZ q G β ≠ 0)) := by sorry

end ZeroFreeRRG.Hardcore
