-- Prove2me | solution 1 for flt5_descent_from_pow4
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T12:27:59.976703+00:00
-- url     : https://prove2.me/submissions/b131641e-9015-434a-9c66-ffc746a49f1c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_flt5_descent_from_pow4
import Theorems.Thm_flt5_coprime_wv
import Theorems.Thm_flt5_descent_construction
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0)
    (h54 : (5 : ℤ) ^ 4 ∣ a + b) :
    ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧
    (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by
  obtain ⟨w, hw⟩ := h54
  obtain ⟨c1, hc1⟩ := h5c
  -- Reconstruct h5c since obtain consumed it
  have h5c : (5 : ℤ) ∣ c := ⟨c1, hc1⟩
  have hPhi_eq : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 =
      5 * (5 ^ 15 * w ^ 4 - 5 ^ 8 * w ^ 2 * (a * b) + (a * b) ^ 2) := by
    have h_b : b = 5 ^ 4 * w - a := by rw [← hw]; ring
    rw [h_b]; ring
  obtain ⟨v, hPhi⟩ : ∃ v : ℤ,
      a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * v :=
    ⟨5 ^ 15 * w ^ 4 - 5 ^ 8 * w ^ 2 * (a * b) + (a * b) ^ 2, hPhi_eq⟩
  have hwv : w * v = c1 ^ 5 := by
    have hfact : a ^ 5 + b ^ 5 =
        (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) := by ring
    have key : (5 : ℤ) ^ 5 * (w * v) = (5 : ℤ) ^ 5 * c1 ^ 5 :=
      calc (5 : ℤ) ^ 5 * (w * v)
          = (5 ^ 4 * w) * (5 * v) := by ring
        _ = (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) := by
              rw [hw, hPhi]
        _ = a ^ 5 + b ^ 5 := hfact.symm
        _ = c ^ 5 := h_eq
        _ = (5 * c1) ^ 5 := by rw [hc1]
        _ = (5 : ℤ) ^ 5 * c1 ^ 5 := by ring
    exact mul_left_cancel₀ (show (5 : ℤ) ^ 5 ≠ 0 from by decide) key
  exact flt5_descent_construction a b c w v c1 h_eq h_cop h5c hc hc1 hw hPhi hwv
    (flt5_coprime_wv a b c w v c1 h_eq h_cop h5c hc hc1 hw hPhi hwv)
