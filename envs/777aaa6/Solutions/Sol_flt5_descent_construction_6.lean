-- Prove2me | solution 6 for flt5_descent_construction
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-14T17:09:59.136684+00:00
-- url     : https://prove2.me/submissions/3b9f5db7-8c29-4d11-bddd-9561b81ca38f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Theorems.Thm_coprime_fifth_power_factor
import Theorems.Thm_flt5_descent_explicit

theorem solution (a b c w v c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * w)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * v)
    (hwv : w * v = c1 ^ 5) (hcop_wv : Int.gcd w v = 1) :
    ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧
    (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by
  obtain ⟨r, hr⟩ := coprime_fifth_power_factor w v c1 hcop_wv hwv
  obtain ⟨s, hs⟩ := coprime_fifth_power_factor v w c1
    (by rw [Int.gcd_comm]; exact hcop_wv) (by rw [mul_comm]; exact hwv)
  exact flt5_descent_explicit a b c w v c1 r s h_eq h_cop h5c hc hc1 hw hPhi hwv hcop_wv hr hs
