-- Prove2me | Theorems.Thm_FactoringLab_fermat_representation_iff
-- name    : FactoringLab.fermat_representation_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:30:44.029549+00:00
-- url     : https://prove2.me/theorems/b8fc5a68-bff0-463f-a52c-03ac02d6f872
-- title:
--   Fermat in disguise (ZZZ).
-- statement:
--   **Fermat in disguise (ZZZ).**  For an odd integer `N`, producing a
--   nontrivial difference-of-squares representation `N = a² - b²` is *equivalent*
--   to producing a nontrivial factorization `N = p * q` with `1 < p ≤ q`.  Any
--   "new" method whose output is a difference of squares is therefore Fermat's
--   method in disguise.
--
--   ```lean
--   theorem FactoringLab.fermat_representation_iff{N : ℤ} (hodd : Odd N) :
--       (∃ a b : ℤ, 0 ≤ b ∧ b + 1 < a ∧ N = a ^ 2 - b ^ 2) ↔
--         (∃ p q : ℤ, 1 < p ∧ p ≤ q ∧ N = p * q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SymmetryCircularity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SymmetryCircularity.lean#L123

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





/-! ### ZZZ: known-method-in-disguise (Fermat) -/

theorem FactoringLab.fermat_representation_iff{N : ℤ} (hodd : Odd N) :
    (∃ a b : ℤ, 0 ≤ b ∧ b + 1 < a ∧ N = a ^ 2 - b ^ 2) ↔
      (∃ p q : ℤ, 1 < p ∧ p ≤ q ∧ N = p * q) := by sorry
