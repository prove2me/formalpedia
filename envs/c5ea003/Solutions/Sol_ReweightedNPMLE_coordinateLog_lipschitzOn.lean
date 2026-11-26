-- Prove2me | solution 1 for ReweightedNPMLE.coordinateLog_lipschitzOn
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:53:29.892918+00:00
-- url     : https://prove2.me/submissions/4b04e113-4993-4b06-a58c-bbbab6527b1b

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_abs_log_sub_log_le_div

/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Coordinatewise logarithm preserves Lipschitzness when all coordinates
have a common positive lower bound. -/
theorem solution {n : ℕ} [Nonempty (Fin n)]
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} {K : ℝ≥0} {c : ℝ}
    (hc : 0 < c) (hvc : ∀ w ∈ s, ∀ i, c ≤ vhat w i)
    (hlip : LipschitzOnWith K vhat s) :
    LipschitzOnWith ⟨(K : ℝ) / c, by positivity⟩
      (fun w i ↦ Real.log (vhat w i)) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro w hw u hu
  rw [dist_eq_norm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))).2
  intro i
  calc
    ‖Real.log (vhat w i) - Real.log (vhat u i)‖ =
        |Real.log (vhat w i) - Real.log (vhat u i)| := Real.norm_eq_abs _
    _ ≤ |vhat w i - vhat u i| / c :=
      abs_log_sub_log_le_div hc (hvc w hw i) (hvc u hu i)
    _ ≤ ‖vhat w - vhat u‖ / c := by
      exact div_le_div_of_nonneg_right
        (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (vhat w - vhat u) i) hc.le
    _ ≤ (K : ℝ) * ‖w - u‖ / c := by
      exact div_le_div_of_nonneg_right
        (by simpa [dist_eq_norm] using hlip.dist_le_mul w hw u hu) hc.le
    _ = ((K : ℝ) / c) * ‖w - u‖ := by ring
