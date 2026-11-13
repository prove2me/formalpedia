-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_edge_properties
-- name    : ZeroFreeRRG.Hardcore.potts_edge_properties
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:50:23.163895+00:00
-- url     : https://prove2.me/theorems/491ce228-5008-4508-b950-fd3d3cd04918
-- title:
--   Potts edge-factor mean, positivity, and integrability
-- statement:
--   Let $q\ge2$, $\beta\ge0$, and let $\nu$ be a simplex-supported Potts cavity law with the prescribed uniform mean. For two independent messages from $\nu$, the Potts edge factor $E$ is nonnegative almost surely and has mean one. Moreover $E$, $E\log E$, and $(1-c+cE)\log(1-c+cE)$ are integrable for every real $c$. This supplies the hypotheses for the entropy comparison in the proof of Lemma 4.17.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed pp. 30–31.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical BigOperators
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem potts_edge_properties (q : ℕ) (hq : 2 ≤ q) (β c : ℝ) (hb : 0 ≤ β)
    (ν : ProbabilityMeasure (Fin q → ℝ)) (hν : ν ∈ cavityLaws (.potts q) β) :
    (∫ p, edgeFactor (.potts q) β p.1 p.2
      ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))) = 1 ∧
    (∀ᵐ p ∂((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))),
      0 ≤ edgeFactor (.potts q) β p.1 p.2) ∧
    Integrable (fun p => edgeFactor (.potts q) β p.1 p.2)
      ((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))) ∧
    Integrable (fun p => xlogx (edgeFactor (.potts q) β p.1 p.2))
      ((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))) ∧
    Integrable (fun p => xlogx (1-c+c*edgeFactor (.potts q) β p.1 p.2))
      ((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ))) := by sorry
end ZeroFreeRRG.Hardcore
