-- Prove2me | solution 1 for TropicalChamberComplex.exchange_mem_wall
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:35:25.946935+00:00
-- url     : https://prove2.me/submissions/53d44c5e-2958-4051-8f7c-e132daf80e66

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









/-! ## Every nonempty subcoalition of the support is a cell label -/


/-! ## The single-voter exchange law -/





open TropicalChamberComplex in
theorem solution[DecidableEq ι] {S : Finset ι} (hS : S.Nonempty) (δ : ι → ℝ) {i j : ι}
    (hiS : i ∈ S) (hjS : j ∈ S) (hij : i ≠ j) {x : ι → ℝ} (hx : x ∈ chamber S δ i) :
    ({i, j} : Finset ι) ⊆ decisiveSet S hS δ (Function.update x j (x i + δ i - δ j)) := by
  classical
  set c : ℝ := x i + δ i - δ j with hc
  set y : ι → ℝ := Function.update x j c with hy
  have hyj : y j = c := by simp [hy]
  have hyk : ∀ k, k ≠ j → y k = x k := by
    intro k hk; simp [hy, Function.update_of_ne hk]
  have hyi : y i = x i := hyk i hij
  have hagg : tropAgg S hS δ y = x i + δ i := by
    refine le_antisymm ?_ ?_
    · have := Finset.inf'_le (fun k => y k + δ k) hiS
      simp only [tropAgg] at this ⊢
      rw [hyi] at this
      exact this
    · refine Finset.le_inf' hS _ ?_
      intro k hk
      by_cases hkj : k = j
      · subst hkj; rw [hyj, hc]; linarith
      · rw [hyk k hkj]; exact hx k hk
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact mem_decisiveSet_iff.mpr ⟨hiS, by rw [hagg, hyi]⟩
  · have hkj : k = j := Finset.mem_singleton.mp hk
    subst hkj
    exact mem_decisiveSet_iff.mpr ⟨hjS, by rw [hagg, hyj, hc]; ring⟩
