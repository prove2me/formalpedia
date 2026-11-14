-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_edge_expectation_transport
-- name    : ZeroFreeRRG.Hardcore.hardcore_edge_expectation_transport
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:21:14.401204+00:00
-- url     : https://prove2.me/theorems/e2f1de40-60bf-447b-af2f-17939df09e9b
-- title:
--   Hardcore edge entropy is invariant under cavity transport
-- statement:
--   The affine hardcore cavity transport preserves the edge-entropy expectation $\mathbb E[E\log E]$ appearing in the Bethe functional.
-- source:
--   Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, proof of Lemma 4.17, pp. 29–31.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option autoImplicit false
open MeasureTheory Set ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.hardcore_edge_expectation_transport (α α' : ℝ) (ha : 0 < α) (hlt : α < α') (ha' : α' < 1/2)
    (ν : ProbabilityMeasure (Fin 2 → ℝ)) (hν : ν ∈ cavityLaws .hardcore α)
    (ν' : ProbabilityMeasure (Fin 2 → ℝ))
    (hmap : (ν' : Measure (Fin 2 → ℝ)) = Measure.map
      (fun x : Fin 2 → ℝ => fun i =>
        (1-(1-α')/(1-α))*(if i.val=1 then 1 else 0) + ((1-α')/(1-α))*x i)
      (ν : Measure (Fin 2 → ℝ))) :
    (∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), xlogx (edgeFactor .hardcore α' p.1 p.2)
      ∂((ν' : Measure (Fin 2 → ℝ)).prod (ν' : Measure (Fin 2 → ℝ)))) =
    ∫ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), xlogx (edgeFactor .hardcore α p.1 p.2)
      ∂((ν : Measure (Fin 2 → ℝ)).prod (ν : Measure (Fin 2 → ℝ))) := by sorry
