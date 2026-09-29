-- Prove2me | solution 1 for AdjSum.not_diagonal_gauss_congruence
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:39:12.72392+00:00
-- url     : https://prove2.me/submissions/4f6a26df-bd69-4e60-831f-5b52c27a809a

-- Sol generated from Applications/AdjacentSumPolytopes/DiagonalGaussCounterexample.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_GaussCongruence
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence

/-!
# The Gauss congruence does *not* localise to a diagonal entry

`GaussCongruence.lean` proves the necklace (Gauss) congruence

`n ∣ ∑_{d ∣ n} μ(n/d) · tr(Mᵈ)`

for the adjacent-sum transfer matrix `M = adjMat s`.  The previous cycle conjectured
(sub-conjecture **S2**) that the congruence *localises*, i.e. that the same divisibility
holds for each fixed diagonal entry `(Mᵈ)_{a,a}` separately, "by the same orbit argument
applied to words with a marked position".

This file refutes that conjecture: the orbit argument cannot be localised, because the
cyclic shift moves the marked position, so the fibres of the shift action on *based*
closed walks are not orbits.

## Main result

* `AdjSum.not_diagonal_gauss_congruence` : for `s = 1`, `n = 2` and the diagonal entry
  `a = 0` one has `∑_{d ∣ 2} μ(2/d) (Mᵈ)_{0,0} = 1`, which is not divisible by `2`.

-- !-- Lab Notes -- !--
* **Experiment.** With `M = adjMat 1 = ![![1,1],![1,0]]` one has `M² = ![![2,1],![1,1]]`,
  so `(M²)_{0,0} − (M)_{0,0} = 2 − 1 = 1`, while the trace version gives
  `tr(M²) − tr(M) = 3 − 1 = 2`, divisible by `2` as the proved theorem requires.
* **Analysis.** A systematic scan over `s ≤ 4`, `n ≤ 8`, `a ≤ s` finds failures for almost
  every triple, e.g. `s = 2, n = 4, a = 0` gives `11`; the successes are sporadic.  The
  quantity `∑_{d∣n} μ(n/d)(Mᵈ)_{a,a}` counts aperiodic closed walks *based at `a`*, and
  the `ℤ/n` action on such walks is not free on the base point — it is only the sum over
  all base points (the trace) that is shift-invariant.
* **Critique.** The refutation is a single explicit computation, but it is not a
  `decide`-only artefact: the two matrix entries are computed from the definition and the
  Möbius values from `ArithmeticFunction.moebius`, and the conclusion is a genuine
  non-divisibility in `ℤ`.
-/

open AdjSum

open Finset

/-- The two matrix entries needed for the counterexample. -/
lemma adjMatZ_one_pow_two_apply : (adjMatZ 1 ^ 2) 0 0 = 2 := by
  rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num [adjMatZ]

lemma adjMatZ_one_pow_one_apply : (adjMatZ 1 ^ 1) 0 0 = 1 := by
  rw [pow_one]
  norm_num [adjMatZ]



open AdjSum in
theorem solution:
    ¬ ∀ (s n : ℕ) (a : Fin (s + 1)), 0 < n →
        (n : ℤ) ∣ ∑ x ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius x.1 : ℤ) * (adjMatZ s ^ x.2) a a := by
  intro h
  have hdvd := h 1 2 0 (by norm_num)
  have hset : (2 : ℕ).divisorsAntidiagonal = {(1, 2), (2, 1)} := by decide
  have hsum : ∑ x ∈ (2 : ℕ).divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℤ) * (adjMatZ 1 ^ x.2) 0 0 = 1 := by
    rw [hset]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    rw [adjMatZ_one_pow_two_apply, adjMatZ_one_pow_one_apply,
      ArithmeticFunction.moebius_apply_one,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    norm_num
  rw [hsum] at hdvd
  norm_num at hdvd
