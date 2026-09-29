-- Prove2me | solution 1 for FactoringLab.factors_determined_by_sum_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:38:40.666984+00:00
-- url     : https://prove2.me/submissions/a2034641-fdb3-46f5-ac17-c30f6bdc5990

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
theorem solution{p q p' q' : ℤ} (hle : p ≤ q) (hle' : p' ≤ q')
    (hprod : p * q = p' * q') (hsum : p + q = p' + q') : p = p' ∧ q = q' := by
  have key : (p - p') * (p - q') = 0 := by
    have : p * p - (p' + q') * p + p' * q' = 0 := by
      rw [← hsum, ← hprod]; ring
    linear_combination this
  have hq : q = p' + q' - p := by linarith
  rcases mul_eq_zero.1 key with h | h
  · have hp : p = p' := by linarith
    exact ⟨hp, by rw [hq, hp]; ring⟩
  · have hp : p = q' := by linarith
    have hq'p : q = p' := by rw [hq, hp]; ring
    have : p' = q' := le_antisymm (by linarith) (by linarith)
    exact ⟨by rw [hp, ← this], by rw [hq'p, this]⟩
