-- Prove2me | solution 1 for TropicalChamberComplex.decisiveSet_locally_decisive
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:35:24.805108+00:00
-- url     : https://prove2.me/submissions/a15fdff1-e18b-4642-ba05-ce61e80e564b

-- Sol generated from Tropical/SocialChoice/ChamberComplex.lean
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


open scoped Classical in
lemma mem_decisiveSet_iff {S : Finset ι} {hS : S.Nonempty} {δ : ι → ℝ} {x : ι → ℝ} {i : ι} :
    i ∈ decisiveSet S hS δ x ↔ i ∈ S ∧ x i + δ i = tropAgg S hS δ x := by
  simp [decisiveSet]


/-- The label is always a nonempty coalition. -/
theorem decisiveSet_nonempty (S : Finset ι) (hS : S.Nonempty) (δ : ι → ℝ) (x : ι → ℝ) :
    (decisiveSet S hS δ x).Nonempty := by
  obtain ⟨i, hiS, hi⟩ := Finset.exists_mem_eq_inf' hS (fun k => x k + δ k)
  exact ⟨i, mem_decisiveSet_iff.mpr ⟨hiS, hi.symm⟩⟩







/-! ## Every nonempty subcoalition of the support is a cell label -/


/-! ## The single-voter exchange law -/





open TropicalChamberComplex in
theorem solution{S : Finset ι} (hS : S.Nonempty) (δ : ι → ℝ)
    {x y : ι → ℝ} (hagree : ∀ i ∈ decisiveSet S hS δ x, y i = x i)
    (hge : ∀ i, x i ≤ y i) :
    tropAgg S hS δ y = tropAgg S hS δ x := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi⟩ := decisiveSet_nonempty S hS δ x
    obtain ⟨hiS, hival⟩ := mem_decisiveSet_iff.mp hi
    calc tropAgg S hS δ y ≤ y i + δ i := Finset.inf'_le (fun k => y k + δ k) hiS
      _ = x i + δ i := by rw [hagree i hi]
      _ = tropAgg S hS δ x := hival
  · refine Finset.le_inf' hS _ ?_
    intro j hj
    have h1 : tropAgg S hS δ x ≤ x j + δ j := Finset.inf'_le (fun k => x k + δ k) hj
    have h2 := hge j
    linarith
