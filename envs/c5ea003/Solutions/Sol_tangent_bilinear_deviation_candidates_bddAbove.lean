-- Prove2me | solution 1 for tangent_bilinear_deviation_candidates_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T09:08:57.813801+00:00
-- url     : https://prove2.me/submissions/3eb5363c-20bb-452a-9048-0505eaac26cf

import Mathlib.Tactic
import Definitions.Def_matrix_completion_talagrand_nested_dual

open MatrixCompletion
open scoped Classical BigOperators

private theorem entry_sq_le_frobeniusNormSq {n₁ n₂ : ℕ}
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    (X i j) ^ 2 ≤ frobeniusNormSq X := by
  unfold frobeniusNormSq
  calc
    (X i j) ^ 2 ≤ ∑ b : Fin n₂, (X i b) ^ 2 := by
      apply Finset.single_le_sum (f := fun b : Fin n₂ => (X i b) ^ 2)
      · intro b _
        positivity
      · exact Finset.mem_univ j
    _ ≤ ∑ a : Fin n₁, ∑ b : Fin n₂, (X a b) ^ 2 := by
      apply Finset.single_le_sum
        (f := fun a : Fin n₁ => ∑ b : Fin n₂, (X a b) ^ 2)
      · intro a _
        positivity
      · exact Finset.mem_univ i

private theorem entry_mem_Icc_of_frobeniusNorm_le_one {n₁ n₂ : ℕ}
    (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hX : frobeniusNorm X ≤ 1) (i : Fin n₁) (j : Fin n₂) :
    X i j ∈ Set.Icc (-1 : ℝ) 1 := by
  have hsq : (X i j) ^ 2 ≤ 1 := by
    have hnorm_sq : frobeniusNormSq X ≤ 1 := by
      have hnonneg : 0 ≤ frobeniusNormSq X := by
        unfold frobeniusNormSq
        positivity
      have hsqrt_nonneg : 0 ≤ Real.sqrt (frobeniusNormSq X) := Real.sqrt_nonneg _
      have hsq_le : (Real.sqrt (frobeniusNormSq X)) ^ 2 ≤ (1 : ℝ) ^ 2 :=
        sq_le_sq' (by linarith) hX
      rwa [Real.sq_sqrt hnonneg, one_pow] at hsq_le
    exact le_trans (entry_sq_le_frobeniusNormSq X i j) hnorm_sq
  have habs : |X i j| ≤ (1 : ℝ) := by
    rw [← Real.sqrt_sq_eq_abs]
    simpa using Real.sqrt_le_sqrt hsq
  exact abs_le.mp habs

private theorem continuous_samplingProjection_pair
    {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂)) :
    Continuous (fun P : Matrix (Fin n₁) (Fin n₂) ℝ ×
        Matrix (Fin n₁) (Fin n₂) ℝ => samplingProjection Omega P.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases hij : (i, j) ∈ Omega
  · simpa [samplingProjection, hij] using
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd))
  · simpa [samplingProjection, hij] using (continuous_const : Continuous fun _ :
        Matrix (Fin n₁) (Fin n₂) ℝ × Matrix (Fin n₁) (Fin n₂) ℝ => (0 : ℝ))

private theorem continuous_tangentProjection_matrix
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    Continuous (fun Y : Matrix (Fin n₁) (Fin n₂) ℝ => tangentProjection S Y) := by
  unfold tangentProjection leftSingularProjection rightSingularProjection
    twoSidedSingularProjection
  fun_prop

private theorem continuous_tangent_bilinear_value
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    Continuous (fun P : Matrix (Fin n₁) (Fin n₂) ℝ ×
        Matrix (Fin n₁) (Fin n₂) ℝ =>
      p⁻¹ *
        matrixInner P.1
          (tangentProjection S (samplingProjection Omega P.2) - p • P.2)) := by
  let A := Matrix (Fin n₁) (Fin n₂) ℝ
  have hX1 : Continuous (fun P : A × A => P.1) := continuous_fst
  have hX2 : Continuous (fun P : A × A => P.2) := continuous_snd
  have hsample : Continuous (fun P : A × A => samplingProjection Omega P.2) :=
    continuous_samplingProjection_pair Omega
  have htan : Continuous
      (fun P : A × A => tangentProjection S (samplingProjection Omega P.2)) :=
    (continuous_tangentProjection_matrix S).comp hsample
  have hscale : Continuous (fun P : A × A => p • P.2) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simpa [Pi.smul_apply, smul_eq_mul] using
      (continuous_const.mul
        ((continuous_apply j).comp ((continuous_apply i).comp hX2)))
  have hfluct : Continuous
      (fun P : A × A =>
        tangentProjection S (samplingProjection Omega P.2) - p • P.2) :=
    htan.sub hscale
  have hinner : Continuous (fun P : A × A =>
      matrixInner P.1
        (tangentProjection S (samplingProjection Omega P.2) - p • P.2)) := by
    unfold matrixInner
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    exact
      (((continuous_apply j).comp ((continuous_apply i).comp hX1)).mul
        ((continuous_apply j).comp ((continuous_apply i).comp hfluct)))
  exact continuous_const.mul hinner

/-- Boundedness of the bilinear candidate set in the Appendix 9.1 flattening
step.

For fixed `Omega`, `S`, and real scalar `p`, the values
`p^{-1} <X1, P_T P_Omega X2 - p X2>` with both Frobenius tests in the unit
ball and `X2` tangent form a bounded-above set.  This is the finite-dimensional
boundedness input needed to use `sSup` when flattening the nested dual
supremum into one supremum over pairs `(X1, X2)`.

Source: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation
(9.2).  The paper passes from the nested dual expression to a supremum over
two test matrices; this formal node isolates the finite-dimensional
boundedness bookkeeping hidden in that passage. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    BddAbove {v : ℝ |
      ∃ X1 X2 : Matrix (Fin n₁) (Fin n₂) ℝ,
        frobeniusNorm X1 ≤ 1 ∧
          tangentProjection S X2 = X2 ∧
            frobeniusNorm X2 ≤ 1 ∧
              v =
                p⁻¹ *
                  matrixInner X1
                    (tangentProjection S (samplingProjection Omega X2) - p • X2)} := by
  let matrixBox : Set (Matrix (Fin n₁) (Fin n₂) ℝ) :=
    Set.univ.pi
      (fun _ : Fin n₁ => Set.univ.pi (fun _ : Fin n₂ => Set.Icc (-1 : ℝ) 1))
  let pairBox : Set
      (Matrix (Fin n₁) (Fin n₂) ℝ × Matrix (Fin n₁) (Fin n₂) ℝ) :=
    Set.prod matrixBox matrixBox
  let F : Matrix (Fin n₁) (Fin n₂) ℝ × Matrix (Fin n₁) (Fin n₂) ℝ → ℝ :=
    fun P =>
      p⁻¹ *
        matrixInner P.1
          (tangentProjection S (samplingProjection Omega P.2) - p • P.2)
  have hbox_compact : IsCompact matrixBox := by
    dsimp [matrixBox]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  have hpair_compact : IsCompact pairBox := by
    dsimp [pairBox]
    exact hbox_compact.prod hbox_compact
  have hpair_nonempty : pairBox.Nonempty := by
    refine ⟨(0, 0), ?_⟩
    refine ⟨?_, ?_⟩
    · dsimp [matrixBox]
      exact Set.mem_univ_pi.mpr
        (fun i => Set.mem_univ_pi.mpr (fun j => by simp))
    · dsimp [matrixBox]
      exact Set.mem_univ_pi.mpr
        (fun i => Set.mem_univ_pi.mpr (fun j => by simp))
  have hF_cont : Continuous F := by
    dsimp [F]
    exact continuous_tangent_bilinear_value Omega S p
  obtain ⟨Pmax, hPmax, hmax⟩ :=
    hpair_compact.exists_isMaxOn hpair_nonempty hF_cont.continuousOn
  refine ⟨F Pmax, ?_⟩
  intro v hv
  rcases hv with ⟨X1, X2, hX1, hT, hX2, rfl⟩
  have hX1_box : X1 ∈ matrixBox := by
    dsimp [matrixBox]
    exact Set.mem_univ_pi.mpr
      (fun i => Set.mem_univ_pi.mpr
        (fun j => entry_mem_Icc_of_frobeniusNorm_le_one X1 hX1 i j))
  have hX2_box : X2 ∈ matrixBox := by
    dsimp [matrixBox]
    exact Set.mem_univ_pi.mpr
      (fun i => Set.mem_univ_pi.mpr
        (fun j => entry_mem_Icc_of_frobeniusNorm_le_one X2 hX2 i j))
  have hpair_mem : (X1, X2) ∈ pairBox := by
    dsimp [pairBox]
    exact ⟨hX1_box, hX2_box⟩
  have hle := (isMaxOn_iff.mp hmax) (X1, X2) hpair_mem
  simpa [F] using hle
