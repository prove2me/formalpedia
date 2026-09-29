-- Prove2me | solution 1 for ClassicalGaps.orientedIncMatrix_row_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T22:43:32.659351+00:00
-- url     : https://prove2.me/submissions/c7511082-05c2-4039-a409-8570f9f84f90

import Mathlib
import Definitions.Def_ClassicalGaps_orientedIncMatrix

open Classical ClassicalGaps

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∑ v : V, orientedIncMatrix G v e = 0 := by
  induction e using Sym2.ind with
  | _ u w =>
  have hne : u ≠ w := G.ne_of_adj (by rwa [SimpleGraph.mem_edgeSet] at he)
  have heq : ∑ v ∈ ({u, w} : Finset V), orientedIncMatrix G v s(u, w) =
      ∑ v : V, orientedIncMatrix G v s(u, w) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    unfold orientedIncMatrix
    simp only [Matrix.of_apply]
    rw [dif_neg]
    rintro ⟨hxin, -⟩
    rw [Sym2.mem_iff] at hxin
    rcases hxin with h1 | h1
    · exact hx.1 h1
    · exact hx.2 h1
  rw [← heq, Finset.sum_pair hne]
  have hu1 : u ∈ (s(u, w) : Sym2 V) := Sym2.mem_mk_left u w
  have hw1 : w ∈ (s(u, w) : Sym2 V) := Sym2.mem_mk_right u w
  have hother_u : Sym2.Mem.other' hu1 = w := by
    have := Sym2.other_spec' hu1
    rw [Sym2.eq_iff] at this
    rcases this with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hne
  have hother_w : Sym2.Mem.other' hw1 = u := by
    have := Sym2.other_spec' hw1
    rw [Sym2.eq_iff] at this
    rcases this with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h hne.symm
    · exact h
  show orientedIncMatrix G u s(u,w) + orientedIncMatrix G w s(u,w) = 0
  unfold orientedIncMatrix
  simp only [Matrix.of_apply]
  rw [dif_pos ⟨hu1, he⟩, dif_pos ⟨hw1, he⟩, hother_u, hother_w]
  rcases lt_or_gt_of_ne (Fintype.equivFin V |>.injective.ne hne) with h | h <;> simp only [Fin.lt_def] at h
  · rw [if_pos h, if_neg (not_lt.mpr h.le)]; ring
  · rw [if_neg (not_lt.mpr h.le), if_pos h]; ring
