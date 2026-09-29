-- Prove2me | Definitions.Def_Probability_TalagrandDuality
-- name    : Probability_TalagrandDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:38:31.634193+00:00
-- url     : https://prove2.me/theorems/a55cd706-4f76-414a-ac0a-faf03ddcba0d
-- title:
--   Aether Catalog definitions — Probability_TalagrandDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.TalagrandDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/TalagrandDuality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_TalagrandDefs

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

namespace Talagrand

open Finset

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-! ### Convexity of the hull -/



/-! ### Attainment of the infimum -/


/-! ### The variational inequality at a minimiser -/




/-! ### The minimax identity -/


/-- The supremum of the admissible weighted Hamming distances to `A`. -/
noncomputable def dTsup (A : Finset (Fin n → α)) (x : Fin n → α) : ℝ :=
  sSup {t : ℝ | ∃ w : Fin n → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, (w i) ^ 2 ≤ 1) ∧ t = dHamming w A x}




end Talagrand


