-- Prove2me | Definitions.Def_Tropical_SocialChoice_ChamberComplex
-- name    : Tropical_SocialChoice_ChamberComplex
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:33:14.654462+00:00
-- url     : https://prove2.me/theorems/cf8bbfdd-d188-4c3c-9904-00f2ff848236
-- title:
--   Aether Catalog definitions — Tropical_SocialChoice_ChamberComplex
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.SocialChoice.ChamberComplex`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/SocialChoice/ChamberComplex.lean by skeleton subtraction
import Mathlib
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

namespace TropicalChamberComplex

open Finset TropicalChambers

variable {ι : Type*}

open scoped Classical in
/-- The decisive coalition at a profile: the voters of the support that attain
the social score. -/
noncomputable def decisiveSet (S : Finset ι) (hS : S.Nonempty) (δ : ι → ℝ) (x : ι → ℝ) :
    Finset ι :=
  S.filter fun i => x i + δ i = tropAgg S hS δ x





/-- The closed cell of a label `T`: the profiles at which every member of `T` is
decisive. -/
def closedCell (S : Finset ι) (hS : S.Nonempty) (δ : ι → ℝ) (T : Finset ι) : Set (ι → ℝ) :=
  {x | T ⊆ decisiveSet S hS δ x}





/-! ## Every nonempty subcoalition of the support is a cell label -/


/-! ## The single-voter exchange law -/




end TropicalChamberComplex


