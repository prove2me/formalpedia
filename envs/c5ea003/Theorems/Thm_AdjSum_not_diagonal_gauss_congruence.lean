-- Prove2me | Theorems.Thm_AdjSum_not_diagonal_gauss_congruence
-- name    : AdjSum.not_diagonal_gauss_congruence
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:14:52.921592+00:00
-- url     : https://prove2.me/theorems/75e6c764-655a-42b5-a768-f23f90ce93bd
-- title:
--   Refutation of the localised Gauss congruence.
-- statement:
--   **Refutation of the localised Gauss congruence.**  The Möbius transform of the
--   sequence of diagonal entries `(Mᵈ)_{a,a}` need not be divisible by `n`.
--
--   ```lean
--   theorem AdjSum.not_diagonal_gauss_congruence:
--       ¬ ∀ (s n : ℕ) (a : Fin (s + 1)), 0 < n →
--           (n : ℤ) ∣ ∑ x ∈ n.divisorsAntidiagonal,
--             (ArithmeticFunction.moebius x.1 : ℤ) * (adjMatZ s ^ x.2) a a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AdjacentSumPolytopes/DiagonalGaussCounterexample.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AdjacentSumPolytopes/DiagonalGaussCounterexample.lean#L51

-- Thm stub generated from Applications/AdjacentSumPolytopes/DiagonalGaussCounterexample.lean
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

theorem AdjSum.not_diagonal_gauss_congruence:
    ¬ ∀ (s n : ℕ) (a : Fin (s + 1)), 0 < n →
        (n : ℤ) ∣ ∑ x ∈ n.divisorsAntidiagonal,
          (ArithmeticFunction.moebius x.1 : ℤ) * (adjMatZ s ^ x.2) a a := by sorry
