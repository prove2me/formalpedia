-- Prove2me | solution 1 for YogeshwaranDM.deficient_hall_matching
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:52:59.827974+00:00
-- url     : https://prove2.me/submissions/94b329d4-a759-4bc3-994f-84475efdf85a

import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic

set_option autoImplicit false

namespace YogeshwaranDM

private theorem matching_card_ge_part {V : Type*} [Fintype V] (G : SimpleGraph V)
    (P Q : Set V) (hG : G.IsBipartiteWith P Q) (M : G.Subgraph)
    (hM : M.IsMatching) (D : Finset V) (hDP : (D : Set V) ⊆ P)
    (hDM : (D : Set V) ⊆ M.verts) : D.card ≤ M.edgeSet.ncard := by
  classical
  let f : D → M.edgeSet := fun x => hM.toEdge ⟨x, hDM x.property⟩
  have hf : Function.Injective f := by
    intro x y he
    have he' := congrArg Subtype.val he
    dsimp [f, SimpleGraph.Subgraph.IsMatching.toEdge] at he'
    rcases Sym2.eq_iff.mp he' with he' | he'
    · exact Subtype.ext he'.1
    · have hyadj := M.adj_sub (hM (hDM y.property)).choose_spec.1
      have hyQ := hG.mem_of_mem_adj (hDP y.property) hyadj
      exact False.elim (hG.disjoint.notMem_of_mem_left (hDP x.property) (he'.1.symm ▸ hyQ))
  have hc := Nat.card_le_card_of_injective f hf
  change Nat.card (D : Set V) ≤ Nat.card M.edgeSet at hc
  simpa only [Nat.card_coe_set_eq, Set.ncard_coe_finset] using hc

end YogeshwaranDM

open YogeshwaranDM

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (L R : Set V)
    (hG : G.IsBipartiteWith L R) (hcover : L ∪ R = Set.univ)
    (d : ℕ) (hd : 1 ≤ d)
    (h : ∀ S : Finset L, S.card - d ≤ (S.biUnion (fun x => G.neighborFinset x)).card) :
    ∃ M : G.Subgraph, M.IsMatching ∧ L.ncard - d ≤ M.edgeSet.ncard := by
  classical
  let A (x : L) : Finset (V ⊕ Fin d) :=
    (G.neighborFinset x).disjSum Finset.univ
  have hA (S : Finset L) : S.card ≤ (S.biUnion A).card := by
    by_cases hS : S.Nonempty
    · have he : S.biUnion A = (S.biUnion (fun x => G.neighborFinset x)).disjSum
          (Finset.univ : Finset (Fin d)) := by
        ext y
        rcases y with y | y
        · simp [A]
        · simp only [A, Finset.mem_biUnion, Finset.inr_mem_disjSum, Finset.mem_univ,
            and_true, iff_true]
          exact hS
      rw [he, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin]
      exact (Nat.sub_le_iff_le_add).mp (h S)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hS]
  obtain ⟨f, hf, hfA⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' A).mp hA
  let U : Finset (V ⊕ Fin d) := Finset.univ.image f
  let Y := U.toLeft
  have hsize : L.ncard - d ≤ Y.card := by
    have hu : U.card = L.ncard := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ]
      simp [← Nat.card_eq_fintype_card]
    have hr : U.toRight.card ≤ d := by
      simpa using Finset.card_le_univ U.toRight
    have hs := U.card_toLeft_add_card_toRight
    rw [hu] at hs
    dsimp [Y]
    omega
  have witness (y : Y) : ∃ x : L, f x = Sum.inl (y : V) := by
    have hy : Sum.inl (y : V) ∈ U := Finset.mem_toLeft.mp y.property
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy
    exact ⟨x, hx⟩
  choose g hg using witness
  have hgadj (y : Y) : G.Adj (g y) y := by
    have ha := hfA (g y)
    rw [hg] at ha
    exact (G.mem_neighborFinset _ _).mp (Finset.inl_mem_disjSum.mp ha)
  have hyR (y : Y) : (y : V) ∈ R := hG.mem_of_mem_adj (g y).property (hgadj y)
  let g' : Y → V := fun y => g y
  have hginj : Function.Injective g' := by
    intro y z he
    have he' : g y = g z := Subtype.ext he
    have he'' : Sum.inl (y : V) = Sum.inl (z : V) := (hg y).symm.trans (he' ▸ hg z)
    exact Subtype.ext (Sum.inl.inj he'')
  have hdisj : Disjoint (Y : Set V) (Set.range g') := by
    apply Set.disjoint_left.mpr
    rintro y hy ⟨z, rfl⟩
    exact hG.disjoint.notMem_of_mem_left (g z).property (hyR ⟨g' z, hy⟩)
  let e : (Y : Set V) ≃ Set.range g' := Equiv.ofInjective g' hginj
  obtain ⟨M, hverts, hM⟩ := SimpleGraph.Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv
    (G := G) hdisj e (fun y => (hgadj y).symm)
  refine ⟨M, hM, hsize.trans ?_⟩
  apply matching_card_ge_part G R L hG.symm M hM Y
  · intro y hy
    exact hyR ⟨y, hy⟩
  · rw [hverts]
    exact Set.subset_union_left
