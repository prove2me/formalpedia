-- Prove2me | solution 1 for SteinENT.no_primitive_representation
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:26:49.194935+00:00
-- url     : https://prove2.me/submissions/7ae615e6-873d-463c-88ef-270d59e9dfe0

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace SteinENT

theorem _root_.solution (n p : ℕ) (hn : 0 < n)
    (hp : p.Prime) (hpn : p ∣ n) (hmod : p % 4 = 3) :
    ¬ ∃ x y : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 ∧ Int.gcd x y = 1 := by
  rintro ⟨x, y, h, hc⟩
  have hnat : n = x.natAbs ^ 2 + y.natAbs ^ 2 := by
    zify
    simpa only [Int.natCast_natAbs, sq_abs] using h
  have hcop : x.natAbs.Coprime y.natAbs := hc
  have hs := ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime hnat hcop
  exact Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one
    (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩) hs hmod

end SteinENT
