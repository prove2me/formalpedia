-- Prove2me | Theorems.Thm_FactoringLab_recovery_from_sum
-- name    : FactoringLab.recovery_from_sum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:30:34.039974+00:00
-- url     : https://prove2.me/theorems/b296749c-6fc9-4ad0-820a-564342ed086d
-- title:
--   The recovery formula.
-- statement:
--   **The recovery formula.**  If the sum `s = p + q` and the product `N = p*q`
--   of two integers `p ≤ q` are known, then `s² - 4N` is the perfect square
--   `(q - p)²` and the two factors are recovered in closed form as
--   `(s ∓ √(s² - 4N))/2`.  This is the engine behind the circularity barrier: any
--   invariant revealing `p + q` factors `N`.
--
--   ```lean
--   theorem FactoringLab.recovery_from_sum{p q s N : ℤ} (hpq : p ≤ q) (hN : N = p * q) (hs : s = p + q) :
--       s ^ 2 - 4 * N = (q - p) ^ 2 ∧
--         (s - (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = p ∧
--         (s + (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SymmetryCircularity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SymmetryCircularity.lean#L78

-- Thm stub generated from Probability/SymmetryCircularity.lean
import Mathlib
import Definitions.Def_Probability_SymmetryCircularity
/-
# Barriers II: symmetry (MMM), computational circularity (TTT),
# and known-method-in-disguise (ZZZ)

* **MMM, the symmetry barrier.**  Every power-sum invariant `p^k + q^k` of the
  hidden factors is a fixed polynomial in the two elementary symmetric
  functions `s = p + q` and `N = p * q` (`FactoringLab.powerSum_eq`).  Hence any
  two factorizations with the same `(N, s)` are indistinguishable by *every*
  symmetric invariant of this family (`FactoringLab.powerSum_congr`).
* **TTT, computational circularity.**  The pair `(N, s)` however *determines*
  the factorization (`FactoringLab.factors_determined_by_sum_prod`), and `s` is
  recoverable from Euler's totient value, so an invariant strong enough to
  break the symmetry barrier already factors `N`.  This is made effective by
  `FactoringLab.factor_recovery_from_totient`, an explicit closed-form recovery
  of `p` and `q` from `N` and `(p-1)(q-1)`.
* **ZZZ, known-method-in-disguise.**  Any method producing a nontrivial
  difference-of-squares representation of an odd `N` is exactly Fermat's method:
  `FactoringLab.fermat_representation_iff` shows the two notions coincide.
-/

open FactoringLab

/-! ### MMM: the symmetry barrier -/




/-! ### TTT: computational circularity -/

theorem FactoringLab.recovery_from_sum{p q s N : ℤ} (hpq : p ≤ q) (hN : N = p * q) (hs : s = p + q) :
    s ^ 2 - 4 * N = (q - p) ^ 2 ∧
      (s - (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = p ∧
      (s + (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = q := by sorry
