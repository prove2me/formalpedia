-- Prove2me | solution 1 for mme_CW_q6_coupled_even_power_finite_extractions_below_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:19:14.579279+00:00
-- url     : https://prove2.me/submissions/aec40af8-1800-47b7-8b95-33ad1f625ea2

import Theorems.Thm_mme_CW_q6_coupled_exact_floor_pruning
import Theorems.Thm_mme_CW_q6_coupled_tensor_extraction_below_raw_of_pruning

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (6 : ℝ) ^ (3 * tau) *
        ((6 : ℝ) ^ (3 * tau) + 2)) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let G : ℕ := N - L
      0 < L ∧ L + G = N ∧ 341 * L < 100 * G ∧
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        V ^ (2 * N) ≤
          ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  have hround := mme_CW_q6_coupled_exact_floor_pruning tau htau
  have hcore :=
    mme_CW_q6_coupled_tensor_extraction_below_raw_of_pruning
      (K := K) tau htau V hV hVlt
  filter_upwards [hround, hcore] with N hround hcore
  dsimp only at hround hcore ⊢
  exact ⟨hround.1, hround.2.1, hround.2.2, hcore hround⟩
