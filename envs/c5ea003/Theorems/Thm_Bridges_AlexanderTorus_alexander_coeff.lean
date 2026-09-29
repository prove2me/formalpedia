-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_coeff
-- name    : Bridges.AlexanderTorus.alexander_coeff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:16:10.377623+00:00
-- url     : https://prove2.me/theorems/c5eed275-cce4-4325-8fee-a7d582a778ee
-- title:
--   Alexander coeff
-- statement:
--   Formal statement of `Bridges.AlexanderTorus.alexander_coeff` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_coeff(N i : ℕ) :
--       (alexander N).coeff i = if i < N then (-1 : ℤ) ^ i else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlexanderKnotNumberBridgeIV.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlexanderKnotNumberBridgeIV.lean#L24

-- Thm stub generated from Bridges/AlexanderKnotNumberBridgeIV.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
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

theorem Bridges.AlexanderTorus.alexander_coeff(N i : ℕ) :
    (alexander N).coeff i = if i < N then (-1 : ℤ) ^ i else 0 := by sorry
