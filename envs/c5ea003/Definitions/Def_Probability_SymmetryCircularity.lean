-- Prove2me | Definitions.Def_Probability_SymmetryCircularity
-- name    : Probability_SymmetryCircularity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:35:08.50314+00:00
-- url     : https://prove2.me/theorems/f317981c-d859-47f2-b081-446f3beb682f
-- title:
--   Aether Catalog definitions — Probability_SymmetryCircularity
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SymmetryCircularity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SymmetryCircularity.lean by skeleton subtraction
import Mathlib
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

namespace FactoringLab

/-! ### MMM: the symmetry barrier -/

/-- The Newton recursion for the power sums of two numbers with elementary
symmetric functions `e₁ = p + q` and `e₂ = p * q`.  Note that it refers only to
`e₁` and `e₂`, never to `p` and `q` separately. -/
def powerSum (e₁ e₂ : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => e₁
  | (k + 2) => e₁ * powerSum e₁ e₂ (k + 1) - e₂ * powerSum e₁ e₂ k



/-! ### TTT: computational circularity -/





/-! ### ZZZ: known-method-in-disguise (Fermat) -/


end FactoringLab


