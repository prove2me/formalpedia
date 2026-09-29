-- Prove2me | solution 1 for HalfPlane.circleArith_isMultiplicative
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:36:31.199427+00:00
-- url     : https://prove2.me/submissions/baf94d71-26c2-4091-a4ce-3e761daa3529

-- Sol generated from MachineLearning/HalfPlaneClosedForm.lean
import Mathlib
import Definitions.Def_MachineLearning_HalfPlaneClosedForm
import Definitions.Def_MachineLearning_HalfPlaneSemiprime
import Theorems.Thm_HalfPlane_circleCount_mul_of_coprime

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
theorem solution: circleArith.IsMultiplicative := by
  constructor
  · decide
  · intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hn : n = 1 := (Nat.coprime_zero_left n).mp hmn
      subst hn
      decide
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hm1 : m = 1 := Nat.coprime_zero_right m |>.mp hmn
      subst hm1
      decide
    haveI : NeZero m := ⟨by omega⟩
    haveI : NeZero n := ⟨by omega⟩
    simpa using circleCount_mul_of_coprime hmn
