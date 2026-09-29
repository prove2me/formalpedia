-- Prove2me | solution 1 for ChebotarevGeodesic.cancellation_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:42:19.561794+00:00
-- url     : https://prove2.me/submissions/33e7e48d-e5a6-4de0-b6cc-28bc403db6b5

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
theorem solution{θ β : ℝ} (hθβ : θ < β) :
    ∃ f g : Fin 2 → ℝ → ℝ,
      HasErrorExponent (fun x => ∑ i, f i x) (fun x => ∑ i, g i x) θ ∧
      ¬ HasErrorExponent (f 0) (g 0) θ ∧ ¬ HasErrorExponent (f 1) (g 1) θ := by
  refine ⟨![fun x => x ^ β, fun x => -(x ^ β)], ![fun _ => 0, fun _ => 0], ?_, ?_, ?_⟩
  · have e₁ : (fun x : ℝ => ∑ i, (![fun x : ℝ => x ^ β, fun x : ℝ => -(x ^ β)] : Fin 2 → ℝ → ℝ) i x)
        = fun _ : ℝ => (0 : ℝ) := by
      funext x
      simp [Fin.sum_univ_two]
    have e₂ : (fun x : ℝ => ∑ i, (![fun _ : ℝ => (0:ℝ), fun _ : ℝ => (0:ℝ)] : Fin 2 → ℝ → ℝ) i x)
        = fun _ : ℝ => (0 : ℝ) := by
      funext x
      simp [Fin.sum_univ_two]
    rw [e₁, e₂]
    exact hasErrorExponent_self _ _
  · refine not_hasErrorExponent_of_growth (c := 1) (β := β) one_pos hθβ fun x hx => ?_
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
    have hxβ : (0 : ℝ) ≤ x ^ β := (Real.rpow_pos_of_pos hx0 β).le
    simp [abs_of_nonneg hxβ]
  · refine not_hasErrorExponent_of_growth (c := 1) (β := β) one_pos hθβ fun x hx => ?_
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
    have hxβ : (0 : ℝ) ≤ x ^ β := (Real.rpow_pos_of_pos hx0 β).le
    simp [abs_of_nonneg hxβ]
