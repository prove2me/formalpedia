-- Prove2me | Theorems.Thm_TropicalChambers_mem_chamber_of_eq_inf_p
-- name    : TropicalChambers.mem_chamber_of_eq_inf_p
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T00:41:29.645017+00:00
-- url     : https://prove2.me/theorems/54cd732a-77da-47f4-a092-5ce4869788a9
-- title:
--   A minimizing voter lies in the corresponding chamber.
-- statement:
--   A minimizing voter lies in the corresponding chamber.
--
--   ```lean
--   theorem TropicalChambers.mem_chamber_of_eq_inf'{S : Finset ι} (hS : S.Nonempty) (δ : ι → ℝ) {x : ι → ℝ}
--       {i : ι} (hi : tropAgg S hS δ x = x i + δ i) : x ∈ chamber S δ i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/SocialChoice/Chambers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/SocialChoice/Chambers.lean#L53

-- Thm stub generated from Tropical/SocialChoice/Chambers.lean
import Mathlib
import Definitions.Def_Tropical_SocialChoice_Chambers
/-
# Polyhedral chambers of social decisiveness

The third face of the tropical/social-choice bridge: the *geometry* of a
min-plus aggregator `F x = min_{i ∈ S} (x i + δ i)`.

For each voter `i` in the tropical support `S` the set of profiles on which `i`
attains the social score is the **chamber**

`chamber S δ i = {x | ∀ j ∈ S, x i + δ i ≤ x j + δ j}`,

an intersection of half-spaces.  The chambers are convex polyhedra, they cover
the whole profile space, `F` is affine (indeed a coordinate projection shifted
by a constant) on each of them, and two chambers meet exactly along the wall
where the two tropical monomials agree.  Finally `F` itself is concave, being a
minimum of affine functions.

Main results: `chamber_convex`, `mem_chamber_of_eq_inf'`, `iUnion_chamber`,
`tropAgg_eq_on_chamber`, `wall_eq`, `tropAgg_concave`.
-/

open TropicalChambers

open Finset

variable {ι : Type*}

theorem TropicalChambers.mem_chamber_of_eq_inf_p{S : Finset ι} (hS : S.Nonempty) (δ : ι → ℝ) {x : ι → ℝ}
    {i : ι} (hi : tropAgg S hS δ x = x i + δ i) : x ∈ chamber S δ i := by sorry
