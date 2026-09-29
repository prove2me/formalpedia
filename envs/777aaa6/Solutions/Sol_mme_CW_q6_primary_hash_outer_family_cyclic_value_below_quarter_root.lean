-- Prove2me | solution 1 for mme_CW_q6_primary_hash_outer_family_cyclic_value_below_quarter_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T05:00:24.591704+00:00
-- url     : https://prove2.me/submissions/a8b0ea0d-8a6a-4373-923d-ae314bc0b5c6

import Theorems.Thm_mme_CW_q6_primary_hash_Ctensor_outer_middle_certificates
import Theorems.Thm_mme_CW_q6_primary_capacity_of_outer_middle_fibers
import Theorems.Thm_mme_CW_q6_primary_profile_capacity_quarter_root
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_cyclic_value_below

open MME Filter Topology

universe u

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let raw : ℝ :=
        4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∀ W : ℝ, 0 ≤ W →
        W < (raw * Real.exp (-(loss / 2))) ^ (2 * N) →
        HasTauValueAtLeast
          (cyclicSymmetrization ((coupledObj K 6).kronPow (2 * N)))
          tau W := by
  have hstars :=
    mme_CW_q6_primary_hash_Ctensor_outer_middle_certificates
      (K := K) tau htau
  have hprofile :=
    mme_CW_q6_primary_profile_capacity_quarter_root tau htau
  filter_upwards [hstars, hprofile] with N hstarsN hprofileN
  dsimp only at hstarsN hprofileN ⊢
  intro hconditions W hW hWlt
  obtain ⟨A, H, _hHpos, _hHbound, stars, houter, hmiddle⟩ :=
    hstarsN hconditions
  let L : ℕ :=
    ⌊(2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ)⌋₊
  let G : ℕ := N - L
  let Z : ℕ :=
    Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
  let X : ℕ := Nat.choose N G
  let B : ℕ := Nat.choose (2 * G) G
  let loss : ℝ :=
    (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
  let capacity : ℝ :=
    ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) /
      (16 * (X : ℝ) ^ 4)
  let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
  let volume : ℕ := 6 ^ (4 * G + 2 * L)
  have hGle : G ≤ N := by
    exact Nat.sub_le _ _
  have hXpos : 0 < X := by
    exact Nat.choose_pos hGle
  have hcapacity :
      capacity * Real.exp (-((N : ℝ) * loss / 2)) ≤
        ((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2 := by
    exact mme_CW_q6_primary_capacity_of_outer_middle_fibers
      N Z X B A H loss hXpos houter hmiddle
  have hside : side = volume := by
    dsimp [side, volume]
    rw [show (36 : ℕ) = 6 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hcube : side * side * side = volume ^ 3 := by
    rw [hside]
    simp [pow_succ]
  apply mme_Ctensor_one_H_one_outer_family_cyclic_value_below
    (stars := Classical.choice stars) tau htau W hW
  calc
    W <
        ((4 * (6 : ℝ) ^ (3 * tau) *
            ((6 : ℝ) ^ (3 * tau) + 2)) *
          Real.exp (-(loss / 2))) ^ (2 * N) := by
            simpa [loss] using hWlt
    _ ≤
        (capacity * Real.exp (-((N : ℝ) * loss / 2))) *
          ((((side * side * side : ℕ) : ℝ)) ^ tau) := by
            simpa [L, G, Z, X, B, capacity, side, loss] using
              hprofileN hconditions
    _ ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          ((((side * side * side : ℕ) : ℝ)) ^ tau) := by
            exact mul_le_mul_of_nonneg_right hcapacity (by positivity)
    _ =
        (A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
          ((((volume ^ 3 : ℕ) : ℝ)) ^ tau) := by
            rw [hcube]
            norm_num
