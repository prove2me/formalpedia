-- Prove2me | Theorems.Thm_Heisenberg125_Heis_commutator_eq_center
-- name    : Heisenberg125.Heis.commutator_eq_center
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:42:43.242404+00:00
-- url     : https://prove2.me/theorems/670ccab8-1883-4319-9895-432b79645cb7
-- title:
--   The commutator subgroup of `Heis p` is its centre.
-- statement:
--   The commutator subgroup of `Heis p` is its centre.
--
--   ```lean
--   theorem Heisenberg125.Heis.commutator_eq_center: commutator (Heis p) = Subgroup.center (Heis p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/Structure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/Structure.lean#L82

-- Thm stub generated from Algebra/Heisenberg125/Structure.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_Structure
/-
# Structure of `H_{p^3}`: matrix realisation, centre, commutator subgroup, exponent

This file justifies the description of `Heis p` used throughout: it *is* the
group of upper unitriangular `3 × 3` matrices over `ZMod p`, its centre and
commutator subgroup both equal `⟨v⟩ ≅ C_p`, it has order `p ^ 3` (so
`|Heis 5| = 125`) and, for odd primes `p`, exponent exactly `p`.
-/

open Heisenberg125

open Heis

variable {p : ℕ}

/-! ## Matrix realisation -/




/-! ## Centre and commutator subgroup -/

theorem Heisenberg125.Heis.commutator_eq_center: commutator (Heis p) = Subgroup.center (Heis p) := by sorry
