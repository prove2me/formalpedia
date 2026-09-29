-- Prove2me | solution 1 for ChebotarevGeodesic.hasLogErrorExponent_mdl_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:59:15.03792+00:00
-- url     : https://prove2.me/submissions/7b04703d-ef10-4dea-bd0a-bc7da9e005f7

-- Sol generated from Shared/ChebotarevGeodesicStaircase.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicStaircase
import Theorems.Thm_ChebotarevGeodesic_HasLogErrorExponent_mono_log
import Theorems.Thm_ChebotarevGeodesic_hasLogErrorExponent_mdl_of_lt
import Theorems.Thm_ChebotarevGeodesic_not_hasLogErrorExponent_mdl_of_lt_exponent
import Theorems.Thm_ChebotarevGeodesic_not_hasLogErrorExponent_mdl_of_lt_log
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


theorem mdl_sub (M : ℝ → ℝ) (K θ : ℝ) (k : ℕ) (x : ℝ) :
    mdl M K θ k x - M x = K * x ^ θ * (Real.log x) ^ k := by
  simp [mdl]

/-- The model sits on its own corner: `(θ, k)` is admissible. -/
theorem hasLogErrorExponent_mdl (M : ℝ → ℝ) {K θ : ℝ} (hK : 0 < K) (k : ℕ) :
    HasLogErrorExponent (mdl M K θ k) M θ k := by
  refine ⟨K, hK, 1, le_rfl, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxθ : (0 : ℝ) < x ^ θ := Real.rpow_pos_of_pos hx0 θ
  rw [mdl_sub, abs_of_nonneg (by positivity)]







open ChebotarevGeodesic in
theorem solution(M : ℝ → ℝ) {K θ θ' : ℝ} (hK : 0 < K) (k j : ℕ) :
    HasLogErrorExponent (mdl M K θ k) M θ' j ↔ (θ < θ' ∨ (θ' = θ ∧ k ≤ j)) := by
  constructor
  · intro h
    rcases lt_trichotomy θ' θ with hlt | heq | hgt
    · exact absurd h (not_hasLogErrorExponent_mdl_of_lt_exponent M hK k j hlt)
    · refine Or.inr ⟨heq, ?_⟩
      by_contra hjk
      push_neg at hjk
      subst heq
      exact not_hasLogErrorExponent_mdl_of_lt_log M hK hjk h
    · exact Or.inl hgt
  · rintro (hlt | ⟨rfl, hkj⟩)
    · exact (hasLogErrorExponent_mdl_of_lt M hK k hlt).mono_log (Nat.zero_le j)
    · exact (hasLogErrorExponent_mdl M hK k).mono_log hkj
