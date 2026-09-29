-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_dihCayley_bergeFulkerson
-- name    : Bridges.InfiniteCubicMatchings.dihCayley_bergeFulkerson
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:24:20.623783+00:00
-- url     : https://prove2.me/theorems/54f11cfe-074a-47b6-8c42-2f25b15ce624
-- title:
--   **An infinite cubic graph satisfying Berge–Fulkerson, arising as a Cayley graph of the
-- statement:
--   **An infinite cubic graph satisfying Berge–Fulkerson, arising as a Cayley graph of the
--   infinite dihedral group on three involutions.**
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.dihCayley_bergeFulkerson: BergeFulkerson dihCayley := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsCayley.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsCayley.lean#L221

-- Thm stub generated from Bridges/InfiniteCubicMatchingsCayley.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCayley
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
/-
# Cayley graphs: infinite cubic Berge–Fulkerson graphs from finite quotients

A cubic Cayley graph `cayley S` of a group `Γ` (with `S` a three-element, inverse-closed
generating set of non-identity elements) is a covering of the Cayley graph of any quotient
`Γ →* Δ` on which the generators stay distinct and nontrivial (`isLocalIsoAt_cayley`).

Combining this with `BergeFulkerson.of_covering` gives a group-theoretic source of infinite
examples:

* `cayley_bergeFulkerson_of_quotient` — if the (possibly finite) quotient Cayley graph
  satisfies Berge–Fulkerson, so does the infinite one upstairs;
* `cayley_bergeFulkerson_of_finite_quotient` — assuming only the *finite* Berge–Fulkerson
  conjecture, every cubic Cayley graph of an infinite group with a suitable finite quotient
  satisfies Berge–Fulkerson;
* `ladderGroup_*` — a concrete instantiation with `Γ = ℤ × ℤ/2`, whose Cayley graph is the
  infinite ladder and whose finite quotients are the prisms.
-/

open Bridges.InfiniteCubicMatchings

universe u v


variable {Γ : Type u} [Group Γ] {Δ : Type v} [Group Δ]


variable (S : Set Γ) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (hS1 : (1 : Γ) ∉ S)












/-! ## A concrete infinite cubic Cayley graph: the ladder group `ℤ × ℤ/2` -/








/-! ## An infinite cubic Cayley graph on three involutions: the infinite dihedral group -/

open DihedralGroup

theorem Bridges.InfiniteCubicMatchings.dihCayley_bergeFulkerson: BergeFulkerson dihCayley := by sorry
