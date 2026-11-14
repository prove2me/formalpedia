-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_perturbation_continuous
-- name    : ZeroFreeRRG.Hardcore.cavity_perturbation_continuous
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:51:36.908501+00:00
-- url     : https://prove2.me/theorems/9c3d3294-a6a1-4f75-8bf4-56d304dcd829
-- title:
--   Continuity of the reveal perturbation on cavity laws
-- statement:
--   For either spin model, the quadratic reveal perturbation appearing in equation (29) is continuous on the cavity-law domain in the weak topology.
-- source:
--   Auxiliary analytic property for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6 and equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option autoImplicit false
open MeasureTheory Set Filter ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.cavity_perturbation_continuous (m : Model) (t : ℝ) (d : ℕ) :
    ContinuousOn (fun ν : ProbabilityMeasure (m.Spin → ℝ) =>
      (d:ℝ) * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
        ∂(ν : Measure (m.Spin → ℝ))) (cavityLaws m t) := by sorry
