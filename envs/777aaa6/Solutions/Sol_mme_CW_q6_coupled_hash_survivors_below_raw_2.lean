-- Prove2me | solution 2 for mme_CW_q6_coupled_hash_survivors_below_raw
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:27:15.810649+00:00
-- url     : https://prove2.me/submissions/b7767529-ccee-40cb-8879-76467dacd37d

import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_block_subtensor
import Theorems.Thm_mme_CW_q6_coupled_even_power_square_extractions_sqrt_loss
import Theorems.Thm_mme_CW_q6_coupled_survivor_square_isomorphic
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss
import Mathlib.Tactic

open MME BigOperators Filter
universe u
set_option autoImplicit false

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
      let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
      (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
      ∃ k : ℕ,
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin k => coupledQ6Survivor K L G))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        V ^ (2 * N) ≤
          (k : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau) := by
  classical
  obtain ⟨D, hD, hcap⟩ :=
    mme_CW_q6_coupled_even_power_square_extractions_sqrt_loss (K := K) tau htau
  let raw : ℝ := 4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  have hraw : 0 < raw := by dsimp [raw]; positivity
  have hsq : V ^ 2 < raw ^ 2 := by
    change V < raw at hVlt
    nlinarith
  have habs := mme_strict_pow_absorbs_sqrt_exp_loss (V ^ 2) (raw ^ 2) D
    (sq_nonneg V) hsq hD
  filter_upwards [hcap, habs] with N hcap habs
  dsimp only
  intro _
  let L : ℕ := ⌊2 / ((6 : ℝ) ^ (3 * tau) + 2) * (N : ℝ)⌋₊
  let G : ℕ := N - L
  let s : ℕ := 6 ^ (4 * G + 2 * L)
  obtain ⟨k, hr, hk⟩ := hcap
  refine ⟨k, ?_, ?_⟩
  · exact (mme_bigAdd_mono_restrict (fun _ : Fin k ↦
      (mme_CW_q6_coupled_survivor_square_isomorphic (K := K) L G).1)).trans hr
  · let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
    have hside : side = s := by
      dsimp [s, side]
      calc
        _ = (6 ^ 2) ^ (2 * G) * 6 ^ (2 * L) := by norm_num
        _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
    change V ^ (2 * N) ≤ (k : ℝ) * (((side * side * side : ℕ) : ℝ) ^ tau)
    rw [hside]
    have hcube : s * s * s = s ^ 3 := by ring
    rw [hcube]
    apply le_trans ?_ hk
    simpa only [← pow_mul] using habs

#print axioms solution
