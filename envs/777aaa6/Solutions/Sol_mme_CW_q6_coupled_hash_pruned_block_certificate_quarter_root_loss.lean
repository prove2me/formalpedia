-- Prove2me | solution 1 for mme_CW_q6_coupled_hash_pruned_block_certificate_quarter_root_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:15:03.021299+00:00
-- url     : https://prove2.me/submissions/39912185-ef22-4597-83e1-0cf3f04b9298

import Theorems.Thm_mme_CW_q6_coupled_primary_hash_Ctensor_quarter_root
import Theorems.Thm_mme_MMObj_square_induced_matching_quarter_root
import Theorems.Thm_mme_Ctensor_induced_matching_survivor_grading_lift
import Theorems.Thm_mme_CW_quarter_root_count_absorption

open MME BigOperators Filter Topology

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let side : ℕ := 36 ^ (2 * Gcount) * 6 ^ (2 * L)
      let raw : ℝ :=
        4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∃ (P : TensorObj K 3) (t : ℕ) (grading : P.TypeGrading t)
          (C : Finset (Fin 3 → Fin t))
          (σs : Fin C.card → (Fin 3 → Fin t)),
        TensorObj.Restrict P
            ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        (∀ j, σs j ∈ C) ∧
        Function.Injective σs ∧
        (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
          ∀ i : Fin 3, σ i ≠ σ' i) ∧
        (∀ σ : Fin 3 → Fin t, σ ∉ C → grading.blockTensor σ = 0) ∧
        (∀ j, TensorObj.Restrict
          (coupledQ6Survivor K L Gcount)
          (grading.blockSubtensor (σs j))) ∧
        (raw * Real.exp (-loss)) ^ (2 * N) ≤
          (C.card : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau) := by
  have hprimary :=
    mme_CW_q6_coupled_primary_hash_Ctensor_quarter_root
      (K := K) tau htau
  have hsecondary :=
    mme_MMObj_square_induced_matching_quarter_root (K := K)
  filter_upwards [hprimary, hsecondary] with N hprimaryN hsecondaryN
  dsimp only at hprimaryN hsecondaryN ⊢
  intro hprofile
  obtain ⟨A, H, hHpos, hHbound, hmacro, hprimaryCount⟩ :=
    hprimaryN hprofile
  obtain ⟨k, hmatching, hsecondaryCount⟩ :=
    hsecondaryN H hHpos hHbound
  obtain ⟨P, t, grading, C, σs, hP, hmem, hinj, hdisj, hsupp,
      hblocks, hcard⟩ :=
    mme_Ctensor_induced_matching_survivor_grading_lift
      (K := K)
      ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N))
      _ _ A H k hmacro hmatching
  refine ⟨P, t, grading, C, σs, hP, hmem, hinj, hdisj, hsupp,
    hblocks, ?_⟩
  rw [hcard]
  apply mme_CW_quarter_root_count_absorption N A H k _ _ _
  · positivity
  · exact hprimaryCount
  · exact hsecondaryCount
