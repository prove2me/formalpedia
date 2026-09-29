-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_cayley_properThreeEdgeColoring_of_involutions
-- name    : Bridges.InfiniteCubicMatchings.cayley_properThreeEdgeColoring_of_involutions
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:24:00.9582+00:00
-- url     : https://prove2.me/theorems/8c6b4987-7985-4fb4-be03-9fac7cadefd6
-- title:
--   Every cubic Cayley graph on three involutions is properly 3-edge-colourable, the
-- statement:
--   **Every cubic Cayley graph on three involutions is properly 3-edge-colourable**, the
--   colour classes being right multiplication by the three generators.  In particular such a
--   graph — finite or infinite — satisfies Berge–Fulkerson.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.cayley_properThreeEdgeColoring_of_involutions(B : Fin 3 → Γ)
--       (hB : Function.Injective B) (hmem : ∀ i, B i ∈ S) (hinvol : ∀ i, B i * B i = 1)
--       (hsub : S ⊆ Set.range B) : ProperThreeEdgeColoring (cayley S hSinv hS1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsCayley.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsCayley.lean#L73

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

theorem Bridges.InfiniteCubicMatchings.cayley_properThreeEdgeColoring_of_involutions(B : Fin 3 → Γ)
    (hB : Function.Injective B) (hmem : ∀ i, B i ∈ S) (hinvol : ∀ i, B i * B i = 1)
    (hsub : S ⊆ Set.range B) : ProperThreeEdgeColoring (cayley S hSinv hS1) := by sorry
