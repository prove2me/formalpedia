-- Prove2me | solution 1 for RootedPathIrregularity.FinGraph.exists_distinct_equal_degree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T03:56:27.215146+00:00
-- url     : https://prove2.me/submissions/fd42a60e-1931-409a-bf81-bb9fe7762109

import Mathlib
import Definitions.Def_Logic_RootedPathIrregularity_Contrarian
open RootedPathIrregularity RootedPathIrregularity.FinGraph in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : FinGraph V)
    (hcard : 2 ≤ Fintype.card V) :
    ∃ v w : V, v ≠ w ∧ G.degree v = G.degree w := by
  by_contra hcon
  push_neg at hcon
  set n := Fintype.card V with hn
  -- degrees lie in `{0, …, n-1}`
  have hsub : ∀ v, G.neighbors v ⊆ Finset.univ.erase v := by
    intro v w hw
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    refine Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ w⟩
    subst h
    rw [G.loopless] at hw
    exact Bool.false_ne_true hw
  have hdeg_le : ∀ v, G.degree v < n := by
    intro v
    have := Finset.card_le_card (hsub v)
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at this
    unfold degree
    omega
  -- pairwise distinct degrees fill `{0, …, n-1}`
  have hinj : Function.Injective G.degree := by
    intro v w h
    by_contra hvw
    exact hcon v w hvw h
  have himage : Finset.univ.image G.degree = Finset.range n := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (hdeg_le v)
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_range, Finset.card_univ]
  obtain ⟨v0, -, hv0⟩ := Finset.mem_image.mp (himage ▸ Finset.mem_range.mpr (by omega : 0 < n))
  obtain ⟨v1, -, hv1⟩ := Finset.mem_image.mp (himage ▸ Finset.mem_range.mpr (by omega : n - 1 < n))
  have hne : v0 ≠ v1 := by
    intro h
    subst h
    omega
  -- the vertex of degree `n - 1` is adjacent to everyone, including the isolated one
  have hfull : G.neighbors v1 = Finset.univ.erase v1 := by
    apply Finset.eq_of_subset_of_card_le (hsub v1)
    rw [Finset.card_erase_of_mem (Finset.mem_univ v1), Finset.card_univ]
    unfold degree at hv1
    omega
  have hadj : G.adj v1 v0 = true := by
    have : v0 ∈ G.neighbors v1 := by
      rw [hfull]
      exact Finset.mem_erase.mpr ⟨hne, Finset.mem_univ v0⟩
    simpa [neighbors] using this
  have hmem : v1 ∈ G.neighbors v0 := by
    simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [G.symm]
    exact hadj
  have : 0 < G.degree v0 := Finset.card_pos.mpr ⟨v1, hmem⟩
  omega
