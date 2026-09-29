-- Prove2me | solution 1 for mme_released_joint_interior_complement_cell_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:12:57.480182+00:00
-- url     : https://prove2.me/submissions/4f63713d-b18a-4633-bed8-b87cdabd57a4

import Theorems.Thm_mme_released_joint_interior_complement_classification
import Theorems.Thm_mme_released_global_boundary_permuted_six_weight_rate
import Theorems.Thm_mme_released_global_empty_permuted_cell_matrix_rate
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge

open BigOperators MME MME.TensorObj MME.ReleasedGlobal MME.ReleasedJointInterior
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.CompleteSplit Filter
universe u
set_option autoImplicit false

private theorem scalar_six_matrix {K : Type u} [Field K] :
    Isomorphic (MMObj K 1 1 1) (sixSymmetrization (oneObj (K := K) (d := 3))) := by
  rw [← TensorQ.toQ_eq_iff]
  change MMq K 1 1 1 = _
  rw [MMq_one]
  simp only [sixSymmetrization, cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, ← TensorQ.permAut_toQ, ← TensorQ.toQ_one, map_one, one_mul]

/-- Each factor complementary to the joint interior has its full boundary rate
or scalar rate zero. One matrix size works for every tolerance and field. -/
theorem solution
    (j : Fin 270) (delta : ℝ) (hdelta : 0 < delta) :
    let c := shapeEquiv (component j).2
    ∃ rate : ℝ,
      ((0 < weight j ∨ coarseCounts (component j).1 c = 0) → rate = 0) ∧
      (¬ 0 < weight j → 0 < coarseCounts (component j).1 c →
        ∃ (z : Fin 3) (B : Boundary.Profile 3 (coarseCounts (component j).1 c)),
          (c.val z).val = 0 ∧
          (∀ i w, wordCounts (component j).1 i c w = B.mu z i w) ∧
          rate = (coarseCounts (component j).1 c : ℝ) * Real.log 2 *
            mme_modern_entropyBits (fun w => (B.count w : ℝ) /
              (coarseCounts (component j).1 c : ℝ)) +
            ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta) ∧
      ∀ᶠ k : ℕ in atTop, ∃ M : ℕ, 0 < M ∧
        (∀ (eps : ℝ), 0 ≤ eps → ∀ (K : Type u) [Field K],
          let L := k * coarseCounts (component j).1 c
          let T := permObj (roleEquiv (component j).1)
            ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L) (fun i x =>
              (∀ r, grade (label 5 3 L (Equiv.refl _) x r) = (c.val i).val) ∧
              if L = 0 then ∀ w, |(profile (component j).1).2 i ⟨0,c⟩ w| ≤ eps
              else ∀ w,
                |(count (fun _ : Fin L => Unit.unit)
                  (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / (L : ℝ) -
                  ((blocks k : ℝ) / (L : ℝ)) * (profile (component j).1).2 i ⟨0,c⟩ w| ≤
                  ((blocks k : ℝ) / (L : ℝ)) * eps))
          Restrict (MMObj K M M M)
            (sixSymmetrization (if 0 < weight j then oneObj else T))) ∧
        ∀ tau : ℝ, 0 ≤ tau → Real.exp (6 * tau * ((k : ℝ) * rate)) ≤
          ((M * M * M : ℕ) : ℝ) ^ tau := by
  classical
  intro c
  by_cases hj : 0 < weight j
  · refine ⟨0, fun _ => rfl, fun hn _ => (hn hj).elim, ?_⟩
    filter_upwards [] with k
    refine ⟨1, by decide, ?_, ?_⟩
    · intro eps heps K _
      dsimp only
      simp only [if_pos hj]
      exact scalar_six_matrix.1
    · intro tau htau
      simp
  · by_cases hc : coarseCounts (component j).1 c = 0
    · refine ⟨0, fun _ => rfl, ?_, ?_⟩
      · intro _ hpos
        exact (Nat.ne_of_gt hpos hc).elim
      · filter_upwards [] with k
        refine ⟨1, by decide, ?_, ?_⟩
        · intro eps heps K _
          dsimp only
          simp only [if_neg hj]
          exact (mme_released_global_empty_permuted_cell_matrix_rate
            (K := K) (roleEquiv (component j).1) (component j).1 k ⟨0,c⟩ hc eps heps 0).1
        · intro tau htau
          simp
    · have hpos := Nat.pos_of_ne_zero hc
      obtain ⟨z, hz⟩ :=
        (mme_released_joint_interior_complement_classification j hj).resolve_left hc
      obtain ⟨B, hmu, hrate⟩ :=
        mme_released_global_boundary_permuted_six_weight_rate.{u}
          (roleEquiv (component j).1) (component j).1 ⟨0,c⟩ hpos z hz delta hdelta
      refine ⟨(coarseCounts (component j).1 c : ℝ) * Real.log 2 *
        mme_modern_entropyBits (fun w => (B.count w : ℝ) /
          (coarseCounts (component j).1 c : ℝ)) +
        ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta, ?_, ?_, ?_⟩
      · rintro (h | h)
        · exact (hj h).elim
        · exact (hc h).elim
      · intro _ _
        exact ⟨z, B, hz, hmu, rfl⟩
      · filter_upwards [hrate] with k hk
        obtain ⟨M, hM, hrestrict, hweight⟩ := hk
        refine ⟨M, hM, ?_, hweight⟩
        intro eps heps K _
        dsimp only
        simp only [if_neg hj]
        exact hrestrict eps heps K


#print axioms solution
