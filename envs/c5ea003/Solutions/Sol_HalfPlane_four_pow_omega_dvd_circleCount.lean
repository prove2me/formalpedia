-- Prove2me | solution 1 for HalfPlane.four_pow_omega_dvd_circleCount
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:43:38.220924+00:00
-- url     : https://prove2.me/submissions/28b6bcf5-349e-41fd-b708-ec4c92e5de7d

-- Sol generated from MachineLearning/HalfPlaneClosedForm.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneCircleBasic
import Definitions.Def_MachineLearning_HalfPlaneClosedForm
import Definitions.Def_MachineLearning_HalfPlaneSemiprime
import Theorems.Thm_HalfPlane_circleCount_odd_squarefree

/-!
# Cycle 4: the separable baseline in closed form

The circle count is an arithmetic function in the technical sense, and it is
multiplicative.  Combined with the odd-prime conic count this gives a closed
product formula for every odd squarefree modulus:

  `C(N) = ∏_{p ∣ N} (p - χ_p(-1))`.

This is the exact "free-witness / CRT-separable" baseline: `C` is computable from the
factorisation of `N` in `O(ω(N))` arithmetic operations, while the non-separable
half-plane count `H` studied in the other files admits no such product formula
(`halfPlaneCount_not_multiplicative`).
-/

open HalfPlane

open Finset






/-! ### Lab notes (cycle 4)

```
N = 15 = 3·5   : (3+1)(5-1) = 16 = C(15)   ✓
N = 21 = 3·7   : (3+1)(7+1) = 32 = C(21)   ✓
N = 35 = 5·7   : (5-1)(7+1) = 32 = C(35)   ✓
N = 105 = 3·5·7: (3+1)(5-1)(7+1) = 128     ✓
```
-/

example : circleCount 15 = 16 := by decide
example : circleCount 21 = 32 := by decide
example : circleCount 35 = 32 := by decide


open HalfPlane in
theorem solution{N : ℕ} (hodd : ¬ 2 ∣ N) (hsq : Squarefree N) :
    4 ^ N.primeFactors.card ∣ circleCount N := by
  rw [circleCount_odd_squarefree hodd hsq, ← Finset.prod_const]
  refine Finset.prod_dvd_prod_of_dvd _ _ ?_
  intro q hq
  have hpq : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hq2 : q ≠ 2 := by
    rintro rfl
    exact hodd (Nat.dvd_of_mem_primeFactors hq)
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hpq.odd_of_ne_two hq2)
  have h2 : 2 ≤ q := hpq.two_le
  by_cases h : q % 4 = 1
  · simp only [h, if_true]
    omega
  · simp only [h, if_false]
    omega
