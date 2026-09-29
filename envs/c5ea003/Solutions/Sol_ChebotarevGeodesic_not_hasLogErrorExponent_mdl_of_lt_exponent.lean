-- Prove2me | solution 1 for ChebotarevGeodesic.not_hasLogErrorExponent_mdl_of_lt_exponent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:57:31.217484+00:00
-- url     : https://prove2.me/submissions/c7d40b58-acb1-453d-972a-e2249dd7579c

-- Sol generated from Shared/ChebotarevGeodesicStaircase.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicStaircase
import Theorems.Thm_ChebotarevGeodesic_log_pow_le
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
theorem solution(M : ℝ → ℝ) {K θ θ' : ℝ} (hK : 0 < K)
    (k j : ℕ) (hθ'θ : θ' < θ) : ¬ HasLogErrorExponent (mdl M K θ k) M θ' j := by
  rintro ⟨C, hC, X, hX, hb⟩
  set δ := (θ - θ') / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hgap : 0 < θ - θ' - δ := by rw [hδdef]; linarith
  set C' := C * ((j + 1) / δ) ^ j with hC'def
  have hC' : 0 < C' := by rw [hC'def]; positivity
  -- pick `x` large enough that `x^(θ-θ'-δ) > C'/K`
  have hbig : Tendsto (fun x : ℝ => x ^ (θ - θ' - δ)) atTop atTop := tendsto_rpow_atTop hgap
  obtain ⟨x, hxX, hxe, hxbig⟩ :
      ∃ x : ℝ, X ≤ x ∧ Real.exp 1 ≤ x ∧ C' / K < x ^ (θ - θ' - δ) := by
    obtain ⟨x, hx⟩ := ((eventually_ge_atTop X).and ((eventually_ge_atTop (Real.exp 1)).and
      (hbig.eventually_gt_atTop (C' / K)))).exists
    exact ⟨x, hx.1, hx.2.1, hx.2.2⟩
  have hx1 : (1 : ℝ) ≤ x := le_trans (Real.one_le_exp (by norm_num)) hxe
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hlog : 1 ≤ Real.log x := one_le_log_of_exp_le hxe
  have hxθ' : (0 : ℝ) < x ^ θ' := Real.rpow_pos_of_pos hx0 θ'
  have hbound := hb x hxX
  rw [mdl_sub, abs_of_nonneg (by positivity)] at hbound
  -- lower bound the left-hand side, upper bound the right-hand side
  have hlow : K * x ^ θ ≤ K * x ^ θ * (Real.log x) ^ k := by
    have h1 : (1 : ℝ) ≤ (Real.log x) ^ k := one_le_pow₀ hlog
    have hxθ : (0 : ℝ) < x ^ θ := Real.rpow_pos_of_pos hx0 θ
    calc K * x ^ θ = K * x ^ θ * 1 := by ring
      _ ≤ K * x ^ θ * (Real.log x) ^ k := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hlogj : (Real.log x) ^ j ≤ ((j + 1) / δ) ^ j * x ^ δ := log_pow_le hδ hx1
  have hhigh : C * x ^ θ' * (Real.log x) ^ j ≤ C' * x ^ (θ' + δ) := by
    have hsplit : x ^ (θ' + δ) = x ^ θ' * x ^ δ := Real.rpow_add hx0 θ' δ
    calc C * x ^ θ' * (Real.log x) ^ j
        ≤ C * x ^ θ' * (((j + 1) / δ) ^ j * x ^ δ) :=
          mul_le_mul_of_nonneg_left hlogj (by positivity)
      _ = C' * (x ^ θ' * x ^ δ) := by rw [hC'def]; ring
      _ = C' * x ^ (θ' + δ) := by rw [hsplit]
  have hkey : K * x ^ θ ≤ C' * x ^ (θ' + δ) := le_trans hlow (le_trans hbound hhigh)
  have hsplit2 : x ^ θ = x ^ (θ - θ' - δ) * x ^ (θ' + δ) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hxpos : (0 : ℝ) < x ^ (θ' + δ) := Real.rpow_pos_of_pos hx0 _
  rw [hsplit2] at hkey
  have hfin : K * x ^ (θ - θ' - δ) ≤ C' := by
    refine le_of_mul_le_mul_right ?_ hxpos
    calc K * x ^ (θ - θ' - δ) * x ^ (θ' + δ)
        = K * (x ^ (θ - θ' - δ) * x ^ (θ' + δ)) := by ring
      _ ≤ C' * x ^ (θ' + δ) := hkey
  rw [div_lt_iff₀ hK] at hxbig
  nlinarith
