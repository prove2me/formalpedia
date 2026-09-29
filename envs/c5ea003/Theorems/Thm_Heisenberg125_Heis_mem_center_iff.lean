-- Prove2me | Theorems.Thm_Heisenberg125_Heis_mem_center_iff
-- name    : Heisenberg125.Heis.mem_center_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:41:52.250885+00:00
-- url     : https://prove2.me/theorems/a08a2158-fb0f-451d-bf04-596dc1bb863f
-- title:
--   An element is central iff its image in `(ZMod p)^2` vanishes, i.e.
-- statement:
--   An element is central iff its image in `(ZMod p)^2` vanishes, i.e. iff it is
--   a power of `v`.
--
--   ```lean
--   theorem Heisenberg125.Heis.mem_center_iff{g : Heis p} :
--       g ∈ Subgroup.center (Heis p) ↔ g.a = 0 ∧ g.b = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/Structure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/Structure.lean#L48

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

theorem Heisenberg125.Heis.mem_center_iff{g : Heis p} :
    g ∈ Subgroup.center (Heis p) ↔ g.a = 0 ∧ g.b = 0 := by sorry
