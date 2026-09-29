-- Prove2me | solution 1 for LinearOptimization.network_incidence_rank
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T03:57:46.118221+00:00
-- url     : https://prove2.me/submissions/cb68f6a3-690b-40c8-956d-c1417359086d

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_NetworkFlowProblem
import Mathlib.Tactic.Linarith

open Matrix

theorem solution {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1))
    (hloop : LinearOptimization.HasNoSelfLoops arcs)
    (hconn : LinearOptimization.IsConnectedNetwork arcs) :
    LinearIndependent ℝ
      (fun i => LinearOptimization.truncatedIncidence arcs i) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg i
  let p : Fin (n + 1) → ℝ := Fin.lastCases 0 g
  have hweighted : ∀ k : Fin m,
      (∑ r : Fin n,
        g r * LinearOptimization.truncatedIncidence arcs r k) =
        p (arcs k).1 - p (arcs k).2 := by
    intro k
    unfold LinearOptimization.truncatedIncidence
      LinearOptimization.incidenceMatrix
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Function.id_def]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    congr 1
    · cases (arcs k).1 using Fin.lastCases with
      | last =>
          simp only [p, Fin.lastCases_last]
          apply Finset.sum_eq_zero
          intro r _
          simp [Ne.symm (Fin.castSucc_ne_last r)]
      | cast r => simp [p]
    · cases (arcs k).2 using Fin.lastCases with
      | last =>
          simp only [p, Fin.lastCases_last]
          apply Finset.sum_eq_zero
          intro r _
          simp [Ne.symm (Fin.castSucc_ne_last r)]
      | cast r => simp [p]
  have hedge : ∀ u v : Fin (n + 1),
      LinearOptimization.networkAdjacent arcs u v → p u = p v := by
    intro u v huv
    obtain ⟨k, hk | hk⟩ := huv
    · have hzero : (∑ r : Fin n,
          g r * LinearOptimization.truncatedIncidence arcs r k) = 0 := by
        have := congrFun hg k
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
      have hdiff := hweighted k
      rw [hk, hzero] at hdiff
      linarith
    · have hzero : (∑ r : Fin n,
          g r * LinearOptimization.truncatedIncidence arcs r k) = 0 := by
        have := congrFun hg k
        simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
      have hdiff := hweighted k
      rw [hk, hzero] at hdiff
      linarith
  have hpath : ∀ u v : Fin (n + 1),
      Relation.ReflTransGen (LinearOptimization.networkAdjacent arcs) u v →
        p u = p v := by
    intro u v huv
    induction huv with
    | refl => rfl
    | tail hab hbc ih => exact ih.trans (hedge _ _ hbc)
  have hi := hpath i.castSucc (Fin.last n) (hconn i.castSucc (Fin.last n))
  simpa [p] using hi
