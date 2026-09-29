-- Prove2me | solution 1 for FactoringLab.totient_semiprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:34:52.687597+00:00
-- url     : https://prove2.me/submissions/ad5fa362-ad77-41e9-b566-aa4992f799c5

-- Sol generated from Probability/SymmetryCircularity.lean
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



open FactoringLab in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Nat.totient (p * q) = (p - 1) * (q - 1) := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).2 hne), Nat.totient_prime hp,
    Nat.totient_prime hq]
