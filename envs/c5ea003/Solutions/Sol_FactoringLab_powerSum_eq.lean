-- Prove2me | solution 1 for FactoringLab.powerSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:50:29.996081+00:00
-- url     : https://prove2.me/submissions/fead70aa-b435-4147-a70d-dfc9657ae042

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
theorem solution(p q : ℤ) : ∀ k : ℕ, powerSum (p + q) (p * q) k = p ^ k + q ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [powerSum]
    | 1 => simp [powerSum]
    | (m + 2) =>
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      rw [show powerSum (p + q) (p * q) (m + 2)
            = (p + q) * powerSum (p + q) (p * q) (m + 1)
              - (p * q) * powerSum (p + q) (p * q) m from rfl, h1, h0]
      ring
