-- Prove2me | solution 2 for Bridges.AlexanderTorus.alexander_coeff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-19T22:20:22.485701+00:00
-- url     : https://prove2.me/submissions/8906188f-4b2d-47ce-857b-af86da72bffd

-- Sol generated from Bridges/AlexanderKnotNumberBridgeIV.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Theorems.Thm_Bridges_AlexanderTorus_alexander_succ
import Theorems.Thm_Bridges_AlexanderTorus_alexander_zero
/-
# The Knot–Number bridge, fourth cycle: coprimality and the size obstruction

Two final structural results.

* **Coprimality bridge** (`alexander_common_divisors_unit_iff_coprime`):
  for odd `M, N > 1`, *every* common divisor of `A_M` and `A_N` in `ℤ[X]` is a unit
  **iff** `gcd(M, N) = 1`. Together with `alexander_dvd_iff_dvd` of cycle III this
  says the map `N ↦ A_N` is an embedding of the divisibility lattice of odd numbers
  into the divisibility lattice of `ℤ[X]`.

* **The size obstruction** (`alexander_support_card`, `alexander_coeff`):
  every one of the `N` coefficients of `A_N` is `±1`, so `A_N` has exactly `N`
  nonzero terms. Writing `A_N` down costs `Θ(N) = Θ(exp(log N))` — this is the
  precise sense in which the bridge is *not* a factoring algorithm.
-/

open Bridges.AlexanderTorus

open Polynomial Finset

/-! ## Coefficients: the size obstruction -/




/-! ## Coprimality bridge -/




open Bridges.AlexanderTorus in
theorem solution(N i : ℕ) :
    (alexander N).coeff i = if i < N then (-1 : ℤ) ^ i else 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
      have hterm : ((-1 : ℤ[X]) ^ n * X ^ n).coeff i = if i = n then (-1 : ℤ) ^ n else 0 := by
        rw [show ((-1 : ℤ[X]) ^ n) = C ((-1 : ℤ) ^ n) by simp [map_pow], coeff_C_mul,
          coeff_X_pow]
        split <;> simp_all
      rw [alexander_succ, coeff_add, ih, hterm]
      rcases lt_trichotomy i n with h | h | h
      · rw [if_pos h, if_neg (by omega), if_pos (by omega), add_zero]
      · subst h
        rw [if_neg (by omega), if_pos rfl, if_pos (by omega), zero_add]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), add_zero]
