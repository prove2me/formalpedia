-- Prove2me | Theorems.Thm_avram_laplace_ae_eq_of_nonnegative_20261026
-- name    : avram_laplace_ae_eq_of_nonnegative_20261026
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:41:52.754298+00:00
-- url     : https://prove2.me/theorems/1587b5db-35ac-4f77-b5fa-77cdd5f1e498
-- title:
--   avram_laplace_ae_eq_of_nonnegative_20261026
-- statement:
--   Automatically extracted helper theorem avram_laplace_ae_eq_of_nonnegative_20261026 from oversized parent candidate f9602c97faae4acee4e776939d04f5ce307193e623a62556976da61261bcbb48.
-- source:
--   candidate-decomposition:cbef8cbe-82d2-46b3-96d5-df0d2a694d20:f9602c97faae4acee4e776939d04f5ce307193e623a62556976da61261bcbb48

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_finiteMeasures_eq_of_complexMGF_eq_on_real_Iio
import Theorems.Thm_AvramDividend_Classical_ae_eq_Ioi_of_exponential_withDensity_eq
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Filter Set Topology ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology
open AvramDividend.Classical

theorem avram_laplace_ae_eq_of_nonnegative_20261026
    (f g : ℝ → ℝ) (b : ℝ)
    (hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * f x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * g x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * f x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * g x) :
    f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g := by sorry
