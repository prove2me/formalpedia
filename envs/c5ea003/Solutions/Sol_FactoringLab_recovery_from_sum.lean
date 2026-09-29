-- Prove2me | solution 1 for FactoringLab.recovery_from_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:34:52.193738+00:00
-- url     : https://prove2.me/submissions/d99961b2-d2ad-4978-be5b-f6f0c8d55a0e

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
theorem solution{p q s N : ℤ} (hpq : p ≤ q) (hN : N = p * q) (hs : s = p + q) :
    s ^ 2 - 4 * N = (q - p) ^ 2 ∧
      (s - (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = p ∧
      (s + (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = q := by
  have hd : s ^ 2 - 4 * N = (q - p) ^ 2 := by rw [hs, hN]; ring
  have hsq : (Int.sqrt (s ^ 2 - 4 * N) : ℤ) = q - p := by
    rw [hd, show (q - p) ^ 2 = (q - p) * (q - p) from by ring, Int.sqrt_eq]
    exact Int.natAbs_of_nonneg (by linarith)
  refine ⟨hd, ?_, ?_⟩
  · rw [hsq, hs, show p + q - (q - p) = 2 * p from by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
  · rw [hsq, hs, show p + q + (q - p) = 2 * q from by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
