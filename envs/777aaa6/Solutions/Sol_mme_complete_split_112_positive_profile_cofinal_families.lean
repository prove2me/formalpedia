-- Prove2me | solution 1 for mme_complete_split_112_positive_profile_cofinal_families
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T00:06:39.338247+00:00
-- url     : https://prove2.me/submissions/de25177d-a006-4b43-9390-ba0e53ce23fa

import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
import Theorems.Thm_mme_primary_hash_uniform_stars_joint_directional_capacity
import Mathlib.Tactic

open MME Filter Topology

set_option autoImplicit false
set_option warningAsError true

/-- The positive-profile finite construction on every compatible rational
subsequence in the established hashing range, with separate A and AH counts. -/
theorem solution (l g : ℕ) (hl : 0 < l) (hbalance : 341 * l < 100 * g) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N : ℕ := (l + g) * m
        let L : ℕ := l * m
        let G : ℕ := g * m
        let Zcount : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
          0 < A ∧ H ≤ 4 ^ N ∧
          (Zcount : ℝ) * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            (A : ℝ) ∧
          (Nat.choose (2 * N) N : ℝ) *
              Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (A : ℝ) * (H : ℝ) := by
  let D := l + g
  have hD : 0 < D := by dsimp [D]; omega
  obtain ⟨C, hC, hlarge⟩ := mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
    (fun n ↦ l * (n / D)) (fun n ↦ g * (n / D))
  refine ⟨C, hC, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hlarge
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with m hm
  have hmpos : 0 < m := by omega
  have hNm : N₀ ≤ D * m :=
    (le_trans (le_max_left _ _) hm).trans (Nat.le_mul_of_pos_left m hD)
  have hdiv : D * m / D = m := Nat.mul_div_cancel_left m hD
  have hLpos : 0 < l * m := Nat.mul_pos hl hmpos
  have hsum : l * m + g * m = D * m := by dsimp [D]; ring
  have hbal : 341 * (l * m) < 100 * (g * m) := by
    simpa only [mul_assoc] using Nat.mul_lt_mul_of_pos_right hbalance hmpos
  have hextract := hN₀ (D * m) hNm
  dsimp only at hextract
  simp only [hdiv] at hextract
  obtain ⟨A, H, family, hH, hA, hmiddle⟩ := hextract ⟨hLpos, hsum, hbal⟩
  rw [hdiv] at family
  have hZpos : (0 : ℝ) < (Nat.choose (2 * (D * m)) (l * m) *
      Nat.choose (2 * (D * m) - l * m) (l * m) : ℕ) := by
    exact_mod_cast Nat.mul_pos
      (Nat.choose_pos (by omega : l * m ≤ 2 * (D * m)))
      (Nat.choose_pos (by omega : l * m ≤ 2 * (D * m) - l * m))
  have hApos : 0 < A := by
    exact_mod_cast lt_of_lt_of_le (mul_pos hZpos (Real.exp_pos _)) hA
  have hcapacity := mme_primary_hash_uniform_stars_joint_directional_capacity
    (D * m) (l * m) (g * m) A H hsum C hA hmiddle
  exact ⟨A, H, family, hApos, hH, hA, hcapacity.2.2⟩
