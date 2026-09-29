-- Prove2me | solution 1 for reindexed_rademacher_matrix_operator_norm_first_moment_log_window_from_2p
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-25T23:30:25.627669+00:00
-- url     : https://prove2.me/submissions/4b2f147b-1b75-4886-b224-5ade8da057a2

import Theorems.Thm_rademacher_matrix_operator_norm_first_moment_log_window_from_2p
import Theorems.Thm_opnorm_submatrix_equiv
import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.EquivFin

open Matrix MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

private theorem submatrix_signed_sum
    {ι α β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (H : ι → Matrix β β ℝ) (eps : Finset ι) :
    (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • (H c).submatrix e e)
      =
    (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c).submatrix e e := by
  ext i j
  simp_rw [Matrix.submatrix_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : c ∈ eps
  · simp [hc, Matrix.submatrix_apply]
  · simp [hc, Matrix.submatrix_apply]

theorem solution :
    ∃ Clog : ℝ, 0 < Clog ∧
      ∀ {ι α : Type*} [Fintype ι] [DecidableEq ι]
        [Fintype α] [DecidableEq α] {N : ℕ},
        0 < Fintype.card α → 2 ≤ N → Fintype.card α ≤ N * N →
        ∀ (H : ι → Matrix α α ℝ),
        (∀ c, (H c).IsHermitian) →
        ∀ (normV : ℝ), 0 ≤ normV →
        let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
        let Hfin : ι → Matrix (Fin (Fintype.card α)) (Fin (Fintype.card α)) ℝ :=
          fun c => (H c).submatrix e e
        (hVHerm : (∑ c : ι, Hfin c * Hfin c).IsHermitian) →
        (∀ i, hVHerm.eigenvalues i ≤ normV) →
        (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
          ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
            (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c)))‖)
        ≤ Clog * Real.sqrt (Real.log (N : ℝ)) * Real.sqrt normV := by
  rcases rademacher_matrix_operator_norm_first_moment_log_window_from_2p with
    ⟨Clog, hClog_pos, hClog⟩
  refine ⟨Clog, hClog_pos, ?_⟩
  intro ι α _ _ _ _ N hcard_pos hN hcard_le H hHHerm normV hnormV
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let Hfin : ι → Matrix (Fin (Fintype.card α)) (Fin (Fintype.card α)) ℝ :=
    fun c => (H c).submatrix e e
  dsimp only
  intro hVHerm hEig
  have hHfinHerm : ∀ c, (Hfin c).IsHermitian := by
    intro c
    exact (hHHerm c).submatrix e
  have hFin :=
    hClog (ι := ι) (d := Fintype.card α) (N := N)
      hcard_pos hN hcard_le Hfin hHfinHerm normV hnormV hVHerm hEig
  have hsum_eq :
      (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
          spectralNorm (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • Hfin c))
        =
      (∑ eps : Finset ι, ((1 : ℝ) / 2) ^ (Fintype.card ι) *
          ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
            (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c)))‖) := by
    apply Finset.sum_congr rfl
    intro eps _
    congr 1
    have hop :=
      opnorm_submatrix_equiv e
        (∑ c : ι, (if c ∈ eps then (1 : ℝ) else -1) • H c)
    rw [spectralNorm]
    rw [submatrix_signed_sum e H eps]
    exact hop
  rwa [hsum_eq] at hFin
