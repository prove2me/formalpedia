-- Prove2me | Theorems.Thm_FactoringLab_factors_determined_by_sum_prod
-- name    : FactoringLab.factors_determined_by_sum_prod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:30:24.439807+00:00
-- url     : https://prove2.me/theorems/60e3a6ac-32a4-468a-9750-4a60581d6274
-- title:
--   The pair `(sum, product)` determines an ordered factorization.
-- statement:
--   The pair `(sum, product)` determines an ordered factorization.  Together
--   with `powerSum_congr` this is the circularity: the *only* extra datum that a
--   symmetric invariant could add to `N` is `p + q`, and that datum already
--   factors `N`.
--
--   ```lean
--   theorem FactoringLab.factors_determined_by_sum_prod{p q p' q' : ℤ} (hle : p ≤ q) (hle' : p' ≤ q')
--       (hprod : p * q = p' * q') (hsum : p + q = p' + q') : p = p' ∧ q = q' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SymmetryCircularity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SymmetryCircularity.lean#L59

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

theorem FactoringLab.factors_determined_by_sum_prod{p q p' q' : ℤ} (hle : p ≤ q) (hle' : p' ≤ q')
    (hprod : p * q = p' * q') (hsum : p + q = p' + q') : p = p' ∧ q = q' := by sorry
