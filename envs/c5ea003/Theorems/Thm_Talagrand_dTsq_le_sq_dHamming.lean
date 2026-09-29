-- Prove2me | Theorems.Thm_Talagrand_dTsq_le_sq_dHamming
-- name    : Talagrand.dTsq_le_sq_dHamming
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:10:11.15582+00:00
-- url     : https://prove2.me/theorems/2666f6e3-d50d-417b-bb96-32e085c8b435
-- title:
--   The hard half of the minimax identity: the convex distance is realised by an
-- statement:
--   The hard half of the minimax identity: the convex distance is realised by an
--   admissible weight vector.
--
--   ```lean
--   theorem Talagrand.dTsq_le_sq_dHamming{A : Finset (Fin n → α)} (hA : A.Nonempty) (x : Fin n → α) :
--       ∃ w : Fin n → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, (w i) ^ 2 ≤ 1) ∧
--         dTsq A x ≤ (dHamming w A x) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/TalagrandDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/TalagrandDuality.lean#L191

-- Thm stub generated from Probability/TalagrandDuality.lean
import Mathlib
import Definitions.Def_Probability_TalagrandDefs
import Definitions.Def_Probability_TalagrandDuality

/-!
# The minimax identity for the convex distance

`Talagrand.dHamming_sq_le_dTsq` is the easy (Cauchy–Schwarz) half of Talagrand's
minimax description of the convex distance: every admissible weighted Hamming
distance is dominated by `d_T`.  This file proves that the inequality is in fact
an **equality**,

`dTsq A x = (sup { dHamming w A x | w ≥ 0, ∑ wᵢ² ≤ 1 })²`,

so that the convex distance *is* the largest weighted Hamming distance.  The
proof is the variational characterisation of the nearest point of a compact
convex set:

* the convex hull of the Hamming vectors is the continuous image of the standard
  simplex on `A`, hence compact, so the infimum defining `dTsq` is attained
  (`Talagrand.exists_dTsq_min`);
* at a minimiser `v` one has `⟨v, u⟩ ≥ ‖v‖²` for every point `u` of the hull
  (`Talagrand.inner_ge_sqn_of_min`), obtained by pushing the expansion of
  `t ↦ ‖(1-t)v + tu‖²` to `t → 0⁺`;
* the normalised minimiser `v/‖v‖` is then an admissible weight vector realising
  the supremum.

## Main results

* `Talagrand.exists_dTsq_min` — the infimum defining `dTsq` is attained.
* `Talagrand.dTsq_le_sq_dHamming` — the hard half of the minimax identity: there
  is an admissible `w` with `dTsq A x ≤ (dHamming w A x)²`.
* `Talagrand.dTsq_eq_sq_dTsup` — the minimax identity `dTsq = (sup …)²`.
-/

open Talagrand

open Finset

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-! ### Convexity of the hull -/



/-! ### Attainment of the infimum -/


/-! ### The variational inequality at a minimiser -/




/-! ### The minimax identity -/

theorem Talagrand.dTsq_le_sq_dHamming{A : Finset (Fin n → α)} (hA : A.Nonempty) (x : Fin n → α) :
    ∃ w : Fin n → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, (w i) ^ 2 ≤ 1) ∧
      dTsq A x ≤ (dHamming w A x) ^ 2 := by sorry
