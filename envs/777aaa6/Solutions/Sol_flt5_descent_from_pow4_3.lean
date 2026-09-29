-- Prove2me | solution 3 for flt5_descent_from_pow4
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T18:11:46.965632+00:00
-- url     : https://prove2.me/submissions/7fb4fa09-0d98-4b8d-a4cb-976701d7e4d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Theorems.Thm_flt5_coprime_wv
import Theorems.Thm_flt5_descent_construction

-- Sketch: flt5_descent_from_pow4
-- Given 5^4 | a+b, extract w, define v = Phi(a,b)/5 via the identity
-- Phi(a,b) = (a+b)^4 - 5*(a*b)*(a+b)^2 + 5*(a*b)^2 = 5*(5^15*w^4 - 5^8*w^2*(a*b) + (a*b)^2)
-- prove w*v=c1^5, gcd(w,v)=1, then apply flt5_descent_construction.

theorem solution (a b c : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0)
    (h54 : (5 : ℤ) ^ 4 ∣ a + b) :
    ∃ a' b' c' : ℤ, a' ^ 5 + b' ^ 5 = c' ^ 5 ∧ Int.gcd a' b' = 1 ∧
    (5 : ℤ) ∣ c' ∧ c' ≠ 0 ∧ c'.natAbs < c.natAbs := by
  obtain ⟨w, hw⟩ := h54
  obtain ⟨c1, hc1⟩ := h5c
  have h5c' : (5 : ℤ) ∣ c := ⟨c1, hc1⟩
  -- v = Phi(a,b)/5 defined via S=a+b, P=a*b identity: Phi = S^4 - 5*P*S^2 + 5*P^2
  set v := 5 ^ 15 * w ^ 4 - 5 ^ 8 * w ^ 2 * (a * b) + (a * b) ^ 2 with hv_def
  have hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * v := by
    rw [hv_def]
    have heq : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 =
               (a + b) ^ 4 - 5 * (a * b) * (a + b) ^ 2 + 5 * (a * b) ^ 2 := by ring
    rw [heq, hw]; ring
  have hwv : w * v = c1 ^ 5 := by
    have key : (5 : ℤ) ^ 5 * (w * v) = (5 : ℤ) ^ 5 * c1 ^ 5 :=
      calc (5 : ℤ) ^ 5 * (w * v)
          = (5 ^ 4 * w) * (5 * v) := by ring
        _ = (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) := by
              rw [hw, hPhi]
        _ = a ^ 5 + b ^ 5 := by ring
        _ = c ^ 5 := h_eq
        _ = (5 * c1) ^ 5 := by rw [hc1]
        _ = (5 : ℤ) ^ 5 * c1 ^ 5 := by ring
    exact mul_left_cancel₀ (show (5 : ℤ) ^ 5 ≠ 0 from by decide) key
  have hcop_wv : Int.gcd w v = 1 :=
    flt5_coprime_wv a b c w v c1 h_eq h_cop h5c' hc hc1 hw hPhi hwv
  exact flt5_descent_construction a b c w v c1 h_eq h_cop h5c' hc hc1 hw hPhi hwv hcop_wv
