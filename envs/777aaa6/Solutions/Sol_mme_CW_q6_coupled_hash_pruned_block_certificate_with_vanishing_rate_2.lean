-- Prove2me | solution 2 for mme_CW_q6_coupled_hash_pruned_block_certificate_with_vanishing_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:25:34.0053+00:00
-- url     : https://prove2.me/submissions/aec2c8e8-fa47-4684-a926-9c527ff28852

import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_block_subtensor
import Theorems.Thm_mme_CW_q6_coupled_even_power_square_extractions_sqrt_loss
import Theorems.Thm_mme_CW_q6_coupled_survivor_square_isomorphic
import Theorems.Thm_mme_uniform_direct_sum_grading_certificate
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss
import Mathlib.Tactic

open MME BigOperators Filter Topology
universe u
set_option autoImplicit false

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ rate : ℕ → ℝ,
      (∀ N, 0 ≤ rate N) ∧
      Tendsto rate atTop (nhds 0) ∧
      ∀ᶠ N : ℕ in atTop,
        let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
        let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
        let Gcount : ℕ := N - L
        let side : ℕ := 36 ^ (2 * Gcount) * 6 ^ (2 * L)
        let raw : ℝ :=
          4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
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
          (raw * Real.exp (-rate N)) ^ (2 * N) ≤
            (C.card : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau) := by
  classical
  obtain ⟨D, hD, hcap⟩ :=
    mme_CW_q6_coupled_even_power_square_extractions_sqrt_loss (K := K) tau htau
  let rate : ℕ → ℝ := fun N ↦ D / Real.sqrt ((N + 1 : ℕ) : ℝ)
  have hrate : ∀ N, 0 ≤ rate N := fun N ↦ div_nonneg hD (Real.sqrt_nonneg _)
  have hnat : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto rate atTop (nhds 0) :=
    (Real.tendsto_sqrt_atTop.comp hnat).const_div_atTop D
  refine ⟨rate, hrate, hlim, ?_⟩
  let raw : ℝ := 4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  filter_upwards [hcap, eventually_ge_atTop (1 : ℕ)] with N hcap hN
  dsimp only
  intro _
  let L : ℕ := ⌊2 / ((6 : ℝ) ^ (3 * tau) + 2) * (N : ℝ)⌋₊
  let G : ℕ := N - L
  let s : ℕ := 6 ^ (4 * G + 2 * L)
  obtain ⟨k, hr, hk⟩ := hcap
  obtain ⟨P, t, grading, C, σs, hP, hmem, hinj, hdisj, hsupp, hblocks, hcard⟩ :=
    mme_uniform_direct_sum_grading_certificate (MMObj K s s s)
      ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) k hr
  refine ⟨P, t, grading, C, σs, hP, hmem, hinj, hdisj, hsupp, ?_, ?_⟩
  · intro j
    exact (mme_CW_q6_coupled_survivor_square_isomorphic (K := K) L G).1.trans
      (hblocks j)
  · let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
    have hside : side = s := by
      dsimp [s, side]
      calc
        _ = (6 ^ 2) ^ (2 * G) * 6 ^ (2 * L) := by norm_num
        _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
    change (raw * Real.exp (-rate N)) ^ (2 * N) ≤ (C.card : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau)
    rw [hcard, hside]
    have hcube : s * s * s = s ^ 3 := by ring
    rw [hcube]
    apply le_trans ?_ hk
    rw [mul_pow, ← Real.exp_nat_mul]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply Real.exp_le_exp.mpr
    have hx : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have hs : 0 < Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hx
    have hsq := Real.sq_sqrt hx.le
    have hn : ((N + 1 : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
      exact_mod_cast (show N + 1 ≤ 2 * N by omega)
    have hmul : D * ((N + 1 : ℕ) : ℝ) ≤ D * ((2 * N : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hn hD
    dsimp [rate]
    apply (mul_le_mul_iff_of_pos_right hs).mp
    field_simp
    nlinarith

#print axioms solution
