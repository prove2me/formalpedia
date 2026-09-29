-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_isLocalIsoAt_cayley
-- name    : Bridges.InfiniteCubicMatchings.isLocalIsoAt_cayley
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:27:15.308039+00:00
-- url     : https://prove2.me/theorems/56fc19f4-07c2-4abb-9979-701e3e07d02b
-- title:
--   A group homomorphism induces a covering of Cayley graphs.
-- statement:
--   **A group homomorphism induces a covering of Cayley graphs.**  If `f` is injective on the
--   connection set `S` and the image connection set avoids the identity, then `f` is a local isomorphism at every
--   vertex from `cayley S` onto the Cayley graph of the image connection set.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.isLocalIsoAt_cayley(f : Γ →* Δ) (hinj : Set.InjOn f S)
--       (hTinv : ∀ t ∈ f '' S, t⁻¹ ∈ f '' S) (hT1 : (1 : Δ) ∉ f '' S) (x : Γ) :
--       IsLocalIsoAt (cayley S hSinv hS1) (cayley (f '' S) hTinv hT1) f x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsCayley.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsCayley.lean#L104

-- Thm stub generated from Bridges/InfiniteCubicMatchingsCayley.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchingsCayley
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
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

theorem Bridges.InfiniteCubicMatchings.isLocalIsoAt_cayley(f : Γ →* Δ) (hinj : Set.InjOn f S)
    (hTinv : ∀ t ∈ f '' S, t⁻¹ ∈ f '' S) (hT1 : (1 : Δ) ∉ f '' S) (x : Γ) :
    IsLocalIsoAt (cayley S hSinv hS1) (cayley (f '' S) hTinv hT1) f x := by sorry
