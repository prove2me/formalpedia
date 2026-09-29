-- Prove2me | solution 1 for ChebotarevGeodesic.hasErrorExponent_of_hasLogErrorExponent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:52:14.698024+00:00
-- url     : https://prove2.me/submissions/14c635bc-8d1d-4305-9f7b-68558a1dfdf8

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





/-! ## The staircase of a model error term

Throughout: `mdl M K θ k` is the counting function `M + K x^θ (log x)^k`. -/










open ChebotarevGeodesic in
theorem solution(h : HasLogErrorExponent π M θ k) :
    HasErrorExponent π M θ := by
  obtain ⟨C, hC, X, hX, hb⟩ := h
  intro ε hε
  refine ⟨C * ((k + 1) / ε) ^ k + 1, by positivity, X, hX, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := le_trans hX hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hxθ : (0 : ℝ) < x ^ θ := Real.rpow_pos_of_pos hx0 θ
  have hlogk : (Real.log x) ^ k ≤ ((k + 1) / ε) ^ k * x ^ ε := log_pow_le hε hx1
  have hsplit : x ^ (θ + ε) = x ^ θ * x ^ ε := Real.rpow_add hx0 θ ε
  have hxε : (0 : ℝ) < x ^ ε := Real.rpow_pos_of_pos hx0 ε
  calc |π x - M x| ≤ C * x ^ θ * (Real.log x) ^ k := hb x hx
    _ ≤ C * x ^ θ * (((k + 1) / ε) ^ k * x ^ ε) :=
        mul_le_mul_of_nonneg_left hlogk (by positivity)
    _ = (C * ((k + 1) / ε) ^ k) * (x ^ θ * x ^ ε) := by ring
    _ ≤ (C * ((k + 1) / ε) ^ k + 1) * (x ^ θ * x ^ ε) := by nlinarith
    _ = (C * ((k + 1) / ε) ^ k + 1) * x ^ (θ + ε) := by rw [hsplit]
