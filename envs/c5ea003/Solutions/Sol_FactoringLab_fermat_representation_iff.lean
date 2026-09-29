-- Prove2me | solution 1 for FactoringLab.fermat_representation_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:38:41.202065+00:00
-- url     : https://prove2.me/submissions/a8b35cf7-42ec-4505-bcc3-412edf2ff11b

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
theorem solution{N : ℤ} (hodd : Odd N) :
    (∃ a b : ℤ, 0 ≤ b ∧ b + 1 < a ∧ N = a ^ 2 - b ^ 2) ↔
      (∃ p q : ℤ, 1 < p ∧ p ≤ q ∧ N = p * q) := by
  constructor
  · rintro ⟨a, b, hb, hba, rfl⟩
    exact ⟨a - b, a + b, by linarith, by linarith, by ring⟩
  · rintro ⟨p, q, hp, hpq, rfl⟩
    -- `N` odd forces both factors odd, so `p + q` and `q - p` are even.
    have hpodd : Odd p := by
      rcases Int.even_or_odd p with hev | h
      · exact absurd hodd (by
          simp [Int.not_odd_iff_even, (hev.mul_right q)])
      · exact h
    have hqodd : Odd q := by
      rcases Int.even_or_odd q with hev | h
      · exact absurd hodd (by
          simp [Int.not_odd_iff_even, (hev.mul_left p)])
      · exact h
    obtain ⟨m, hm⟩ := hpodd
    obtain ⟨n, hn⟩ := hqodd
    refine ⟨m + n + 1, n - m, by omega, by omega, ?_⟩
    rw [hm, hn]; ring
