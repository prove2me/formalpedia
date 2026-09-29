-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_support_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:56:00.6724+00:00
-- url     : https://prove2.me/submissions/89dd2d24-16ca-4a4a-8911-e1b35981ff76

-- Sol generated from Bridges/AlexanderKnotNumberBridgeIV.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Theorems.Thm_Bridges_AlexanderTorus_alexander_coeff
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


/-- Every coefficient of `A_N` below the degree is `±1`, hence nonzero: the support of
`A_N` is all of `{0, …, N-1}`. -/
theorem alexander_support (N : ℕ) : (alexander N).support = Finset.range N := by
  ext i
  rw [Polynomial.mem_support_iff, alexander_coeff, Finset.mem_range]
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    exact h rfl
  · intro h
    rw [if_pos h]
    exact pow_ne_zero i (by norm_num)


/-! ## Coprimality bridge -/




open Bridges.AlexanderTorus in
theorem solution(N : ℕ) : (alexander N).support.card = N := by
  rw [alexander_support, Finset.card_range]
