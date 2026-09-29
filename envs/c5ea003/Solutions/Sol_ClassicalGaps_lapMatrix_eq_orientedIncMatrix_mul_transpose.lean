-- Prove2me | solution 1 for ClassicalGaps.lapMatrix_eq_orientedIncMatrix_mul_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T20:24:53.744526+00:00
-- url     : https://prove2.me/submissions/8808bf6e-f393-468d-ae66-b72c863ff95f

import Mathlib
import Definitions.Def_ClassicalGaps_orientedIncMatrix

open Classical Matrix Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem incMatrix_eq_of_mem (i : V) (e : Sym2 V) (h : i ∈ e ∧ e ∈ G.edgeSet) :
    G.incMatrix ℝ i e = 1 :=
  G.incMatrix_of_mem_incidenceSet ⟨h.2, h.1⟩

private theorem incMatrix_eq_of_notMem (i : V) (e : Sym2 V) (h : ¬(i ∈ e ∧ e ∈ G.edgeSet)) :
    G.incMatrix ℝ i e = 0 :=
  G.incMatrix_of_notMem_incidenceSet fun hc => h ⟨hc.2, hc.1⟩

private theorem oriented_sq (i : V) (e : Sym2 V) :
    ClassicalGaps.orientedIncMatrix G i e * ClassicalGaps.orientedIncMatrix G i e =
      G.incMatrix ℝ i e := by
  by_cases h : i ∈ e ∧ e ∈ G.edgeSet
  · rw [incMatrix_eq_of_mem G i e h]
    unfold ClassicalGaps.orientedIncMatrix
    simp only [Matrix.of_apply]
    rw [dif_pos h]
    split_ifs <;> ring
  · rw [incMatrix_eq_of_notMem G i e h]
    unfold ClassicalGaps.orientedIncMatrix
    simp only [Matrix.of_apply]
    rw [dif_neg h]
    ring

private theorem oriented_mul_of_ne {i j : V} (hij : i ≠ j) (e : Sym2 V) :
    ClassicalGaps.orientedIncMatrix G i e * ClassicalGaps.orientedIncMatrix G j e =
      - (G.incMatrix ℝ i e * G.incMatrix ℝ j e) := by
  by_cases hi : i ∈ e ∧ e ∈ G.edgeSet
  · by_cases hj : j ∈ e ∧ e ∈ G.edgeSet
    · have he : e = s(i, j) := (Sym2.mem_and_mem_iff hij).mp ⟨hi.1, hj.1⟩
      subst he
      unfold ClassicalGaps.orientedIncMatrix
      simp only [Matrix.of_apply]
      rw [dif_pos hi, dif_pos hj]
      have hoi : Sym2.Mem.other' hi.1 = j := by
        have hspec := Sym2.other_spec' hi.1
        rcases Sym2.eq_iff.mp hspec with ⟨_, hb⟩ | ⟨ha, _⟩
        · exact hb
        · exact absurd ha hij
      have hoj : Sym2.Mem.other' hj.1 = i := by
        have hspec := Sym2.other_spec' hj.1
        rcases Sym2.eq_iff.mp hspec with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact absurd ha.symm hij
        · exact hb
      rw [hoi, hoj, incMatrix_eq_of_mem G i _ hi, incMatrix_eq_of_mem G j _ hj]
      have hne : (Fintype.equivFin V i).val ≠ (Fintype.equivFin V j).val := fun h =>
        hij ((Fintype.equivFin V).injective (Fin.ext h))
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [if_pos hlt, if_neg (not_lt.mpr hlt.le)]; ring
      · rw [if_neg (not_lt.mpr hgt.le), if_pos hgt]; ring
    · rw [incMatrix_eq_of_notMem G j e hj]
      unfold ClassicalGaps.orientedIncMatrix
      simp only [Matrix.of_apply]
      rw [dif_neg hj]
      ring
  · rw [incMatrix_eq_of_notMem G i e hi]
    unfold ClassicalGaps.orientedIncMatrix
    simp only [Matrix.of_apply]
    rw [dif_neg hi]
    ring

theorem solution :
    G.lapMatrix ℝ = ClassicalGaps.orientedIncMatrix G * (ClassicalGaps.orientedIncMatrix G)ᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  by_cases hij : i = j
  · subst hij
    simp_rw [oriented_sq G i]
    have hdeg : (∑ e, G.incMatrix ℝ i e) = (G.degree i : ℝ) := SimpleGraph.sum_incMatrix_apply G
    rw [hdeg]
    have hadiag : (G.adjMatrix ℝ) i i = 0 := by
      have := congrFun (G.diag_adjMatrix (α := ℝ)) i
      simpa [Matrix.diag] using this
    rw [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
        Matrix.diagonal_apply_eq, hadiag, sub_zero]
  · simp_rw [oriented_mul_of_ne G hij]
    rw [Finset.sum_neg_distrib]
    have hmul : (∑ e, G.incMatrix ℝ i e * G.incMatrix ℝ j e) =
        (G.incMatrix ℝ * (G.incMatrix ℝ)ᵀ) i j := by
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    rw [hmul, SimpleGraph.incMatrix_mul_transpose]
    simp only [Matrix.of_apply, if_neg hij]
    rw [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
        Matrix.diagonal_apply_ne _ hij, zero_sub, SimpleGraph.adjMatrix_apply]
