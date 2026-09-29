-- Prove2me | solution 1 for mme_CW_q6_coupled_hash_pruned_block_certificate_below_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T15:48:59.739894+00:00
-- url     : https://prove2.me/submissions/f7b43578-cbe6-4b25-b798-a240f02b99a7

import Theorems.Thm_mme_CW_q6_coupled_hash_pruned_block_certificate_with_vanishing_rate

open MME BigOperators Filter Topology

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
      let Gcount : ℕ := N - L
      let side : ℕ := 36 ^ (2 * Gcount) * 6 ^ (2 * L)
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
        V ^ (2 * N) ≤
          (C.card : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau) := by
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  obtain ⟨rate, _hrate_nonneg, hrate, hcert⟩ :=
    mme_CW_q6_coupled_hash_pruned_block_certificate_with_vanishing_rate
      (K := K) tau htau
  have hneg : Tendsto (fun N : ℕ => -rate N) atTop (nhds 0) := by
    simpa only [neg_zero] using hrate.neg
  have hexp :
      Tendsto (fun N : ℕ => Real.exp (-rate N)) atTop (nhds 1) := by
    simpa only [Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp hneg
  have hscaled :
      Tendsto (fun N : ℕ => raw * Real.exp (-rate N)) atTop (nhds raw) := by
    simpa only [mul_one] using tendsto_const_nhds.mul hexp
  have hbelow : ∀ᶠ N : ℕ in atTop, V ≤ raw * Real.exp (-rate N) :=
    (hscaled.eventually_const_lt (by simpa only [raw] using hVlt)).mono
      (fun _ h => h.le)
  filter_upwards [hcert, hbelow] with N hcert hbase
  dsimp only at hcert ⊢
  intro hprune
  obtain ⟨P, t, grading, C, σs, hP, hmem, hinj, hdisj, hsupp,
    hcomponent, hcount⟩ := hcert hprune
  refine ⟨P, t, grading, C, σs, hP, hmem, hinj, hdisj, hsupp,
    hcomponent, ?_⟩
  exact (pow_le_pow_left₀ hV hbase (2 * N)).trans (by
    simpa only [raw] using hcount)
