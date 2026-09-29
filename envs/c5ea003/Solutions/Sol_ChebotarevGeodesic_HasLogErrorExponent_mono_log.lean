-- Prove2me | solution 1 for ChebotarevGeodesic.HasLogErrorExponent.mono_log
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:40:36.103435+00:00
-- url     : https://prove2.me/submissions/96fdde5e-ab5c-4ac2-a813-21feb8b51938

-- Sol generated from Shared/ChebotarevGeodesicStaircase.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicStaircase
/-
# The two-parameter exponent staircase

Fifth research cycle on the paper *"Chebotarev geodesic theorem: non-split case"*.

`HasErrorExponent π M θ` (the shape "exponent `θ + ε`") deliberately forgets logarithmic
factors: `Shared.ChebotarevGeodesicTransfer` proves `optimalExponent (M + K x^θ log^k x) M = θ`
for every `k`.  The natural question left open there is what the `ε` actually hides.  This
file answers it completely for the model error terms produced by trace formulae.

We introduce the **two-parameter, `ε`-free** predicate

  `HasLogErrorExponent π M θ k  :  |π x − M x| ≤ C x^θ (log x)^k  for large x`,

show that its truth region is a *staircase* (upward closed in both parameters) whose
projection to the first coordinate recovers `HasErrorExponent`, and then compute the region
exactly for `π = M + K x^θ (log x)^k`:

  `HasLogErrorExponent π M θ' j ↔ θ < θ' ∨ (θ' = θ ∧ k ≤ j)`.

So the region has a single corner, at `(θ, k)`, and both coordinates of that corner are
genuine invariants of the pair `(π, M)`: the exponent `θ` *and* the log power `k`.  In
particular an error term `x^{25/36} (log x)^k` is not compatible with `x^{25/36} (log x)^{k−1}`,
which is precisely the information destroyed by writing "exponent `25/36 + ε`".
-/


open Finset Filter
open scoped Topology

open ChebotarevGeodesic


variable {π M : ℝ → ℝ} {θ θ' : ℝ} {k j : ℕ}

/-- `1 ≤ log x` for `x ≥ e`; the basic fact behind monotonicity in the log parameter. -/
theorem one_le_log_of_exp_le {x : ℝ} (hx : Real.exp 1 ≤ x) : 1 ≤ Real.log x :=
  (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hx)).mpr hx




/-! ## The staircase of a model error term

Throughout: `mdl M K θ k` is the counting function `M + K x^θ (log x)^k`. -/










open ChebotarevGeodesic in
theorem solution(h : HasLogErrorExponent π M θ k) (hkj : k ≤ j) :
    HasLogErrorExponent π M θ j := by
  obtain ⟨C, hC, X, hX, hb⟩ := h
  refine ⟨C, hC, max X (Real.exp 1), le_trans hX (le_max_left _ _), fun x hx => ?_⟩
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog : 1 ≤ Real.log x := one_le_log_of_exp_le hxe
  have hx1 : (1 : ℝ) ≤ x := le_trans hX hxX
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxθ : (0 : ℝ) < x ^ θ := Real.rpow_pos_of_pos hx0 θ
  have hpow : (Real.log x) ^ k ≤ (Real.log x) ^ j := pow_le_pow_right₀ hlog hkj
  calc |π x - M x| ≤ C * x ^ θ * (Real.log x) ^ k := hb x hxX
    _ ≤ C * x ^ θ * (Real.log x) ^ j := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
