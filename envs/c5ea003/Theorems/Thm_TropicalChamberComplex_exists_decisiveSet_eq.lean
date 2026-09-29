-- Prove2me | Theorems.Thm_TropicalChamberComplex_exists_decisiveSet_eq
-- name    : TropicalChamberComplex.exists_decisiveSet_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:39:17.464644+00:00
-- url     : https://prove2.me/theorems/a4554443-7d59-4036-affc-bfb311583365
-- title:
--   Completeness of the labelling.
-- statement:
--   **Completeness of the labelling.**  For every nonempty `T ⊆ S` there is a
--   profile whose decisive coalition is exactly `T`.  Hence the cells of the complex
--   are labelled precisely by the nonempty subcoalitions of the tropical support.
--
--   ```lean
--   theorem TropicalChamberComplex.exists_decisiveSet_eq{S : Finset ι} (hS : S.Nonempty) (δ : ι → ℝ) {T : Finset ι}
--       (hTS : T ⊆ S) (hT : T.Nonempty) :
--       ∃ x : ι → ℝ, decisiveSet S hS δ x = T := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/SocialChoice/ChamberComplex.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/SocialChoice/ChamberComplex.lean#L124

-- Thm stub generated from Tropical/SocialChoice/ChamberComplex.lean
import Mathlib
import Definitions.Def_Tropical_SocialChoice_ChamberComplex
import Definitions.Def_Tropical_SocialChoice_Chambers
/-
# The cell complex of decisive coalitions, and the single-voter exchange law

This file completes the geometric half of the tropical/social-choice bridge
started in `Tropical/SocialChoice/Chambers.lean`.

For a min-plus aggregator `F x = min_{i ∈ S} (x i + δ i)` the *decisive
coalition at a profile* `x` is the set

`decisiveSet S δ x = {i ∈ S | x i + δ i = F x}`

of voters attaining the social score.  The cells of the induced complex are the
level sets of this labelling map, and the closed cells are exactly the finite
intersections of the chambers of `Chambers.lean`, hence convex polyhedra.

Main results.

* `decisiveSet_nonempty`, `mem_decisiveSet_iff_mem_chamber`: the labelling is
  well defined and matches the chamber description.
* `closedCell_eq_iInter`, `closedCell_convex`: the closed cell of a label `T` is
  `⋂ i ∈ T, chamber S δ i`, a convex polyhedron.
* `decisiveSet_locally_decisive`: the label really is a *decisive coalition* —
  the social score is unchanged by any raising of the scores of the voters
  outside it.
* `exists_decisiveSet_eq`: every nonempty `T ⊆ S` occurs as a label, so the
  labels of the complex are exactly the nonempty subcoalitions of the support.
* `exchange_mem_wall`, `decisiveSet_update_eq_singleton`, `single_voter_exchange`:
  the **single-voter exchange law**.  From any profile in the chamber of `i` one
  reaches the wall between the chambers of `i` and `j`, and then the open cell
  labelled `{j}`, by changing the score of the single voter `j`.  Adjacency of
  top-dimensional cells is thus governed by one-voter exchanges.
-/

open TropicalChamberComplex

open Finset TropicalChambers

variable {ι : Type*}











/-! ## Every nonempty subcoalition of the support is a cell label -/

theorem TropicalChamberComplex.exists_decisiveSet_eq{S : Finset ι} (hS : S.Nonempty) (δ : ι → ℝ) {T : Finset ι}
    (hTS : T ⊆ S) (hT : T.Nonempty) :
    ∃ x : ι → ℝ, decisiveSet S hS δ x = T := by sorry
