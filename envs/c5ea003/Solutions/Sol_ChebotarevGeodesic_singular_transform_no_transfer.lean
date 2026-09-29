-- Prove2me | solution 1 for ChebotarevGeodesic.singular_transform_no_transfer
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:01:53.550615+00:00
-- url     : https://prove2.me/submissions/8cef82e9-c4ef-428d-895e-be6d798a8c18

-- Sol generated from Shared/ChebotarevGeodesicTransfer.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTransfer
import Theorems.Thm_ChebotarevGeodesic_hasErrorExponent_self
import Theorems.Thm_ChebotarevGeodesic_not_hasErrorExponent_of_growth
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





/-! ## 1.  C1: an invertible transform transports the whole exponent set -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]










/-! ## 2.  C2: the rank obstruction -/





/-! ## 3.  C3: powers of the logarithm do not move the optimal exponent -/



/-! ## 4.  C5: a converse Chebotarev principle -/




/-! ## 5.  Synthesis for the setting of the paper -/



/-! ## 6.  C4: a quantitative equidistribution rate -/




open ChebotarevGeodesic in
omit [DecidableEq ι] in
theorem solution(A : Matrix ι ι ℝ) (v : ι → ℝ)
    (hv : A.mulVec v = 0) (M : ι → ℝ → ℝ) {θ β : ℝ} (hθβ : θ < β) {i : ι} (hvi : v i ≠ 0) :
    ∃ f : ι → ℝ → ℝ,
      (∀ j, HasErrorExponent (transform A f j) (transform A M j) θ) ∧
      ¬ HasErrorExponent (f i) (M i) θ := by
  refine ⟨fun k x => M k x + v k * x ^ β, fun j => ?_, ?_⟩
  · have hz : ∑ k, A j k * v k = 0 := by
      have := congrFun hv j
      simpa [Matrix.mulVec, dotProduct] using this
    have e : transform A (fun k x => M k x + v k * x ^ β) j = transform A M j := by
      funext x
      have hsplit : ∑ k, A j k * (M k x + v k * x ^ β)
          = (∑ k, A j k * M k x) + (∑ k, A j k * v k) * x ^ β := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      simp only [transform]
      rw [hsplit, hz, zero_mul, add_zero]
    rw [e]
    exact hasErrorExponent_self _ _
  · refine not_hasErrorExponent_of_growth (c := |v i|) (β := β) (abs_pos.mpr hvi) hθβ ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
    have hxβ : (0 : ℝ) ≤ x ^ β := (Real.rpow_pos_of_pos hx0 β).le
    have heq : M i x + v i * x ^ β - M i x = v i * x ^ β := by ring
    show |v i| * x ^ β ≤ |M i x + v i * x ^ β - M i x|
    rw [heq, abs_mul, abs_of_nonneg hxβ]
