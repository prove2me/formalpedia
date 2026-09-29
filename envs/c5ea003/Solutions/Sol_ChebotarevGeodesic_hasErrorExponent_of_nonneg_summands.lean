-- Prove2me | solution 1 for ChebotarevGeodesic.hasErrorExponent_of_nonneg_summands
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:42:21.52917+00:00
-- url     : https://prove2.me/submissions/6c8f6ddd-53e8-4f9e-8dc9-8f317ca3b96d

-- Sol generated from Shared/ChebotarevGeodesicTransfer.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Definitions.Def_Shared_ChebotarevGeodesicOptimal
import Definitions.Def_Shared_ChebotarevGeodesicTransfer
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
theorem solution{ι : Type*} (s : Finset ι) (f g : ι → ℝ → ℝ)
    (θ : ℝ) (hnn : ∀ i ∈ s, ∀ᶠ x in atTop, 0 ≤ f i x - g i x)
    (hsum : HasErrorExponent (fun x => ∑ i ∈ s, f i x) (fun x => ∑ i ∈ s, g i x) θ)
    {i : ι} (hi : i ∈ s) : HasErrorExponent (f i) (g i) θ := by
  intro ε hε
  obtain ⟨C, hC, X, hX, hb⟩ := hsum ε hε
  have hall : ∀ᶠ x in atTop, ∀ j ∈ s, 0 ≤ f j x - g j x :=
    (eventually_all_finset s).mpr hnn
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hall
  refine ⟨C, hC, max X (max X₀ 1),
    le_max_of_le_right (le_max_right _ _), fun x hx => ?_⟩
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hxX₀ : X₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right X _)) hx
  have hnn' : ∀ j ∈ s, 0 ≤ f j x - g j x := hX₀ x hxX₀
  have h1 : f i x - g i x ≤ ∑ j ∈ s, (f j x - g j x) := Finset.single_le_sum hnn' hi
  have h2 : ∑ j ∈ s, (f j x - g j x) = (∑ j ∈ s, f j x) - ∑ j ∈ s, g j x :=
    Finset.sum_sub_distrib (fun j => f j x) (fun j => g j x)
  have h3 : (∑ j ∈ s, f j x) - ∑ j ∈ s, g j x ≤ C * x ^ (θ + ε) :=
    le_trans (le_abs_self _) (hb x hxX)
  rw [h2] at h1
  rw [abs_of_nonneg (hnn' i hi)]
  linarith
