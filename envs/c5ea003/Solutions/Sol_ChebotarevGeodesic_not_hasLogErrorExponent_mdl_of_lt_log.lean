-- Prove2me | solution 1 for ChebotarevGeodesic.not_hasLogErrorExponent_mdl_of_lt_log
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:57:31.79118+00:00
-- url     : https://prove2.me/submissions/76d5edff-1a04-4418-b43a-5622c0124c8a

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


theorem mdl_sub (M : ℝ → ℝ) (K θ : ℝ) (k : ℕ) (x : ℝ) :
    mdl M K θ k x - M x = K * x ^ θ * (Real.log x) ^ k := by
  simp [mdl]








open ChebotarevGeodesic in
theorem solution(M : ℝ → ℝ) {K θ : ℝ} (hK : 0 < K) {k j : ℕ}
    (hjk : j < k) : ¬ HasLogErrorExponent (mdl M K θ k) M θ j := by
  rintro ⟨C, hC, X, hX, hb⟩
  -- pick `x` large: `x ≥ X`, `x ≥ e`, and `log x > C / K`
  obtain ⟨x, hxX, hxe, hxlog⟩ :
      ∃ x : ℝ, X ≤ x ∧ Real.exp 1 ≤ x ∧ C / K < Real.log x := by
    obtain ⟨x, hx⟩ := ((eventually_ge_atTop X).and ((eventually_ge_atTop (Real.exp 1)).and
      (Real.tendsto_log_atTop.eventually_gt_atTop (C / K)))).exists
    exact ⟨x, hx.1, hx.2.1, hx.2.2⟩
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hxe
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxθ : (0 : ℝ) < x ^ θ := Real.rpow_pos_of_pos hx0 θ
  have hlog : 1 ≤ Real.log x := one_le_log_of_exp_le hxe
  have hlogpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le one_pos hlog
  have hbound := hb x hxX
  rw [mdl_sub, abs_of_nonneg (by positivity)] at hbound
  -- `log^k ≥ log^(j+1)`
  have hstep : (Real.log x) ^ (j + 1) ≤ (Real.log x) ^ k :=
    pow_le_pow_right₀ hlog hjk
  have h1 : K * x ^ θ * (Real.log x) ^ (j + 1) ≤ C * x ^ θ * (Real.log x) ^ j := by
    calc K * x ^ θ * (Real.log x) ^ (j + 1)
        ≤ K * x ^ θ * (Real.log x) ^ k :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ C * x ^ θ * (Real.log x) ^ j := hbound
  have hlogj : (0 : ℝ) < (Real.log x) ^ j := by positivity
  have h2 : K * Real.log x ≤ C := by
    have hexp : K * x ^ θ * (Real.log x) ^ (j + 1)
        = (K * Real.log x) * (x ^ θ * (Real.log x) ^ j) := by ring
    have hexp' : C * x ^ θ * (Real.log x) ^ j = C * (x ^ θ * (Real.log x) ^ j) := by ring
    rw [hexp, hexp'] at h1
    have hposf : (0 : ℝ) < x ^ θ * (Real.log x) ^ j := by positivity
    exact le_of_mul_le_mul_right (by linarith [h1]) hposf
  rw [div_lt_iff₀ hK] at hxlog
  linarith
