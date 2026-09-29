-- Prove2me | Theorems.Thm_Bridges_AlexanderTorus_alexander_common_divisors_unit_iff_coprime
-- name    : Bridges.AlexanderTorus.alexander_common_divisors_unit_iff_coprime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:17:22.552195+00:00
-- url     : https://prove2.me/theorems/f3b3e268-2ec8-4007-ae88-0d17c130021d
-- title:
--   Coprimality bridge.
-- statement:
--   **Coprimality bridge.** For odd `M, N > 1`: the Alexander polynomials of `T(2,M)`
--   and `T(2,N)` have only unit common divisors iff `M` and `N` are coprime.
--
--   ```lean
--   theorem Bridges.AlexanderTorus.alexander_common_divisors_unit_iff_coprime{M N : ℕ} (hM : Odd M) (hN : Odd N)
--       (hM1 : 1 < M) (hN1 : 1 < N) :
--       (∀ f : ℤ[X], f ∣ alexander M → f ∣ alexander N → IsUnit f) ↔ Nat.Coprime M N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlexanderKnotNumberBridgeIV.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlexanderKnotNumberBridgeIV.lean#L73

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




/-! ## Coprimality bridge -/

theorem Bridges.AlexanderTorus.alexander_common_divisors_unit_iff_coprime{M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hM1 : 1 < M) (hN1 : 1 < N) :
    (∀ f : ℤ[X], f ∣ alexander M → f ∣ alexander N → IsUnit f) ↔ Nat.Coprime M N := by sorry
