-- Prove2me | solution 1 for ChebotarevGeodesic.optimalExponent_log_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:01:24.49132+00:00
-- url     : https://prove2.me/submissions/e6aa2b1c-648c-4795-a733-543c0336543e

-- Sol generated from Shared/ChebotarevGeodesicTransfer.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTransfer
import Theorems.Thm_ChebotarevGeodesic_hasErrorExponent_of_log_pow_bound
import Theorems.Thm_ChebotarevGeodesic_hasErrorExponent_optimalExponent
import Theorems.Thm_ChebotarevGeodesic_not_hasErrorExponent_of_eventually_growth
import Theorems.Thm_ChebotarevGeodesic_optimalExponent_le_of_hasErrorExponent
/-
# Chebotarev geodesic theorem: transfer, obstruction, and converse

A fourth research cycle built on `Shared.ChebotarevGeodesic`,
`Shared.ChebotarevGeodesicSharpness` and `Shared.ChebotarevGeodesicOptimal`.

The previous cycles produced the exponent calculus, the invertible-transform reduction
(the abstract form of the paper's reduction of the non-split case to the split case), the
structure theorem `exponentSet = Ici (optimalExponent)`, and sharpness examples.  This file
resolves, inside that framework, three of the conjectures that were left open:

* **C1 (transport of the whole exponent set).**  An invertible transform of a family of
  counting functions does not merely transfer one admissible exponent: it induces an
  *equality of joint exponent sets*, hence of joint optimal exponents
  (`jointExponentSet_transform`, `jointOptimalExponent_transform`).

* **C2 (a rank obstruction).**  The invertibility hypothesis is not an artefact of the proof.
  For a *singular* transform there are families whose transforms are exact and whose
  individual optimal exponents are arbitrarily large (`singular_transform_no_transfer`,
  `det_zero_no_transfer`), and in fact the transfer principle holds for a matrix `A`
  **iff** `det A ≠ 0` (`transfer_iff_det_ne_zero`).

* **C3 (log powers are invisible).**  `optimalExponent (M + K x^θ log^k x) M = θ` exactly
  (`optimalExponent_log_pow`): the `ε` in "`25/36 + ε`" hides log powers and nothing more.

* **C5 (a converse Chebotarev principle).**  If the class-counting functions dominate their
  main terms then the single aggregate estimate implies all the individual ones
  (`hasErrorExponent_of_nonneg_summands`, `chebotarev_converse`), and the positivity
  hypothesis cannot be dropped (`cancellation_counterexample`).

Supporting the above, the sharpness machinery of cycle 3 is upgraded from "growth for all
`x ≥ 1`" to "growth eventually", which is what genuine oscillation estimates provide.
-/


open Finset Filter Set
open scoped Topology

open ChebotarevGeodesic

/-! ## 0.  Robustness of the exponent predicate -/


/-! ### Eventual growth suffices for sharpness

`not_hasErrorExponent_of_growth` requires the lower bound `c x^β ≤ |π − M|` for *all* `x ≥ 1`.
Oscillation estimates only ever hold for large `x`; we upgrade the three sharpness statements
accordingly. -/


/-- Eventual growth of size `x^β` bounds the exponent set from below by `β`. -/
theorem bddBelow_exponentSet_of_eventually_growth {π M : ℝ → ℝ} {β c : ℝ} (hc : 0 < c)
    (hgrow : ∀ᶠ x in atTop, c * x ^ β ≤ |π x - M x|) :
    BddBelow (exponentSet π M) := by
  refine ⟨β, fun θ hθ => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact not_hasErrorExponent_of_eventually_growth hc hlt hgrow hθ

/-- Eventual growth of size `x^β` forces `optimalExponent ≥ β`. -/
theorem le_optimalExponent_of_eventually_growth {π M : ℝ → ℝ} {β c : ℝ} (hc : 0 < c)
    (hne : (exponentSet π M).Nonempty)
    (hgrow : ∀ᶠ x in atTop, c * x ^ β ≤ |π x - M x|) :
    β ≤ optimalExponent π M := by
  by_contra hlt
  push_neg at hlt
  exact not_hasErrorExponent_of_eventually_growth hc hlt hgrow
    (hasErrorExponent_optimalExponent π M hne)

/-- **Bracketing from eventual growth.** -/
theorem optimalExponent_eq_of_eventually_growth {π M : ℝ → ℝ} {β c : ℝ} (hc : 0 < c)
    (hgrow : ∀ᶠ x in atTop, c * x ^ β ≤ |π x - M x|)
    (hupper : HasErrorExponent π M β) :
    optimalExponent π M = β :=
  le_antisymm
    (optimalExponent_le_of_hasErrorExponent
      (bddBelow_exponentSet_of_eventually_growth hc hgrow) hupper)
    (le_optimalExponent_of_eventually_growth hc ⟨β, hupper⟩ hgrow)

/-! ## 1.  C1: an invertible transform transports the whole exponent set -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]










/-! ## 2.  C2: the rank obstruction -/





/-! ## 3.  C3: powers of the logarithm do not move the optimal exponent -/



/-! ## 4.  C5: a converse Chebotarev principle -/




/-! ## 5.  Synthesis for the setting of the paper -/



/-! ## 6.  C4: a quantitative equidistribution rate -/




open ChebotarevGeodesic in
theorem solution(M : ℝ → ℝ) {K θ : ℝ} (hK : 0 < K) (k : ℕ) :
    optimalExponent (fun x => M x + K * x ^ θ * (Real.log x) ^ k) M = θ := by
  have hupper : HasErrorExponent (fun x => M x + K * x ^ θ * (Real.log x) ^ k) M θ := by
    refine hasErrorExponent_of_log_pow_bound (K := K) (k := k) hK.le fun x hx => ?_
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    have hxθ : (0 : ℝ) < x ^ θ := Real.rpow_pos_of_pos hx0 θ
    have heq : M x + K * x ^ θ * (Real.log x) ^ k - M x = K * x ^ θ * (Real.log x) ^ k := by
      ring
    rw [heq, abs_of_nonneg (by positivity)]
  have hgrow : ∀ᶠ x in atTop,
      K * x ^ θ ≤ |(M x + K * x ^ θ * (Real.log x) ^ k) - M x| := by
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos 1) hx
    have hlog : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
    have hlk : 1 ≤ (Real.log x) ^ k := one_le_pow₀ hlog
    have hxθ : (0 : ℝ) < x ^ θ := Real.rpow_pos_of_pos hx0 θ
    have heq : M x + K * x ^ θ * (Real.log x) ^ k - M x = K * x ^ θ * (Real.log x) ^ k := by
      ring
    rw [heq, abs_of_nonneg (by positivity)]
    have hKx : (0 : ℝ) ≤ K * x ^ θ := by positivity
    calc K * x ^ θ = K * x ^ θ * 1 := by ring
      _ ≤ K * x ^ θ * (Real.log x) ^ k := mul_le_mul_of_nonneg_left hlk hKx
  exact optimalExponent_eq_of_eventually_growth hK hgrow hupper
