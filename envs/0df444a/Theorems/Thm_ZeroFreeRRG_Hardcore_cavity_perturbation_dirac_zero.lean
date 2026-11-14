-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_cavity_perturbation_dirac_zero
-- name    : ZeroFreeRRG.Hardcore.cavity_perturbation_dirac_zero
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:45:46.840217+00:00
-- url     : https://prove2.me/theorems/fabdda77-6c4e-447f-9614-fd20f1f001c8
-- title:
--   The perturbation vanishes at the replica-symmetric point
-- statement:
--   If every coordinate of the model marginal is nonzero, the normalized interaction sends the marginal to the all-ones vector, and the quadratic perturbation in equation (29) vanishes at its Dirac law.
-- source:
--   Auxiliary model identity for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, p. 39, proof of Lemma 5.6 and equation (29).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open MeasureTheory ZeroFreeRRG.Hardcore
open scoped Classical BigOperators

theorem ZeroFreeRRG.Hardcore.cavity_perturbation_dirac_zero (m : Model) (t : ℝ) (d : ℕ) (hπ : ∀ a, m.pi t a ≠ 0) :
    (∀ a, Mmul m t (m.pi t) a = 1) ∧
    (d:ℝ) * ∫ μ, (∑ a, m.pi t a * (Mmul m t μ a - 1)^2)
      ∂((diracPi m t : ProbabilityMeasure (m.Spin → ℝ)) : Measure (m.Spin → ℝ)) = 0 := by sorry
