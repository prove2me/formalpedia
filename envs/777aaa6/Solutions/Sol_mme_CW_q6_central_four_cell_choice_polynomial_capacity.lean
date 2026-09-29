-- Prove2me | solution 1 for mme_CW_q6_central_four_cell_choice_polynomial_capacity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:32:02.392752+00:00
-- url     : https://prove2.me/submissions/9cc8e67c-6b25-4f7e-a9b3-5801b2570690

import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Sum
import Theorems.Thm_mme_two_pow_le_succ_mul_central_choose

set_option autoImplicit false
set_option warningAsError true

/-- The four-cell central choices occupy at least a polynomial fraction of
all coordinate halves. -/
theorem solution
    {n L G : ℕ} (hLG : L + G = 2 * n) :
    Nat.choose (2 * (2 * n)) (2 * n) ≤
      (2 * n + 1) ^ 4 *
        ((Nat.choose L (L / 2) * Nat.choose L (L / 2)) *
          (Nat.choose G (n - L / 2) * Nat.choose G (n - L / 2))) := by
  let cL := Nat.choose L (L / 2)
  let cG := Nat.choose G (G / 2)
  have hindex : n - L / 2 = G - G / 2 := by omega
  have hchooseG : Nat.choose G (n - L / 2) = cG := by
    rw [hindex]
    exact Nat.choose_symm (Nat.div_le_self G 2)
  have hL := mme_two_pow_le_succ_mul_central_choose L
  have hG := mme_two_pow_le_succ_mul_central_choose G
  change 2 ^ L ≤ (L + 1) * cL at hL
  change 2 ^ G ≤ (G + 1) * cG at hG
  have hL2 : (2 ^ L) ^ 2 ≤ ((L + 1) * cL) ^ 2 :=
    Nat.pow_le_pow_left hL 2
  have hG2 : (2 ^ G) ^ 2 ≤ ((G + 1) * cG) ^ 2 :=
    Nat.pow_le_pow_left hG 2
  have hpow : 2 ^ (2 * (2 * n)) ≤
      ((L + 1) ^ 2 * (G + 1) ^ 2) * (cL ^ 2 * cG ^ 2) := by
    calc
      2 ^ (2 * (2 * n)) = (2 ^ L) ^ 2 * (2 ^ G) ^ 2 := by
        rw [show 2 * (2 * n) = (L + G) * 2 by omega, pow_mul, pow_add]
        ring
      _ ≤ ((L + 1) * cL) ^ 2 * ((G + 1) * cG) ^ 2 :=
        Nat.mul_le_mul hL2 hG2
      _ = ((L + 1) ^ 2 * (G + 1) ^ 2) * (cL ^ 2 * cG ^ 2) := by ring
  have hLbound : L + 1 ≤ 2 * n + 1 := by omega
  have hGbound : G + 1 ≤ 2 * n + 1 := by omega
  have hcoeff : (L + 1) ^ 2 * (G + 1) ^ 2 ≤ (2 * n + 1) ^ 4 := by
    calc
      (L + 1) ^ 2 * (G + 1) ^ 2 ≤
          (2 * n + 1) ^ 2 * (2 * n + 1) ^ 2 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hLbound 2)
          (Nat.pow_le_pow_left hGbound 2)
      _ = (2 * n + 1) ^ 4 := by ring
  calc
    Nat.choose (2 * (2 * n)) (2 * n) ≤ 2 ^ (2 * (2 * n)) :=
      Nat.choose_le_two_pow _ _
    _ ≤ ((L + 1) ^ 2 * (G + 1) ^ 2) * (cL ^ 2 * cG ^ 2) := hpow
    _ ≤ (2 * n + 1) ^ 4 * (cL ^ 2 * cG ^ 2) :=
      Nat.mul_le_mul_right (cL ^ 2 * cG ^ 2) hcoeff
    _ = (2 * n + 1) ^ 4 *
        ((Nat.choose L (L / 2) * Nat.choose L (L / 2)) *
          (Nat.choose G (n - L / 2) * Nat.choose G (n - L / 2))) := by
      rw [hchooseG]
      dsimp [cL, cG]
      ring
