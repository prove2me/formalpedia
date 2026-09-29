-- Prove2me | solution 1 for mme_complete_split_112_first_slice_uniform_stars_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T22:31:40.66316+00:00
-- url     : https://prove2.me/submissions/c8ede20d-b47d-426b-b926-6ef43b9df917

import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
import Mathlib.Tactic

open MME Filter Topology

set_option autoImplicit false
set_option warningAsError true

/-- Uniform induced families on the exact released-profile subsequence,
with the original separate outer-fiber and shared-fiber count losses. -/
theorem solution :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N : ℕ := 1180591620717411303424 * m
        let L : ℕ := 8959763742786037 * m
        let G : ℕ := 1180582660953668517387 * m
        let Zcount : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        ∃ A H : ℕ,
          ∃ _family : CWQ6PrimaryHashFamily N L G A H,
            0 < A ∧ H ≤ 4 ^ N ∧
            (Zcount : ℝ) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              (A : ℝ) ∧
            (middle : ℝ) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  let D : ℕ := 1180591620717411303424
  let l : ℕ := 8959763742786037
  let g : ℕ := 1180582660953668517387
  obtain ⟨C, hC, hlarge⟩ := mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
    (fun n ↦ l * (n / D)) (fun n ↦ g * (n / D))
  refine ⟨C, hC, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hlarge
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with m hm
  have hmpos : 0 < m := by omega
  have hNm : N₀ ≤ D * m := by dsimp [D]; omega
  have hdiv : D * m / D = m := by dsimp [D]; omega
  have hLpos : 0 < l * m := Nat.mul_pos (by decide) hmpos
  have hsum : l * m + g * m = D * m := by dsimp [l, g, D]; omega
  have hbalance : 341 * (l * m) < 100 * (g * m) := by
    dsimp [l, g]
    omega
  have hextract := hN₀ (D * m) hNm
  dsimp only at hextract
  simp only [hdiv] at hextract
  obtain ⟨A, H, family, hH, hA, hmiddle⟩ :=
    hextract ⟨hLpos, hsum, hbalance⟩
  rw [hdiv] at family
  refine ⟨A, H, family, ?_, hH, hA, hmiddle⟩
  have hZpos :
      (0 : ℝ) < (Nat.choose (2 * (D * m)) (l * m) *
        Nat.choose (2 * (D * m) - l * m) (l * m) : ℕ) := by
    exact_mod_cast Nat.mul_pos
      (Nat.choose_pos (by omega : l * m ≤ 2 * (D * m)))
      (Nat.choose_pos (by omega : l * m ≤ 2 * (D * m) - l * m))
  have hApos : (0 : ℝ) < A :=
    lt_of_lt_of_le (mul_pos hZpos (Real.exp_pos _)) hA
  exact_mod_cast hApos
