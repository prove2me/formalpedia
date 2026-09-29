-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PrimitiveRecordBarrier
-- name    : ErdosProblems_Erdos243_PrimitiveRecordBarrier
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:29:03.306233+00:00
-- url     : https://prove2.me/theorems/8a5caeb8-1127-408d-a01b-7e2054c638c6
-- title:
--   Running maximum of the numerator
-- statement:
--   Defines the running maximum of a natural sequence and proves that each current value lies below it. Record-growth contradictions are separate theorem cards.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PrimitiveRecordBarrier.lean#L1-L571
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PrimitiveRecordBarrier is the versioned native alias of original module ErdosProblems.Erdos243.PrimitiveRecordBarrier.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

/-!
# Erdős 243: prime-power barriers for record numerator jumps

This module formalises the finite arithmetic of the record-jump barrier for a
*dynamically reduced* reciprocal tail, i.e. one in which an arbitrary
cancellation factor `hc n` is removed at every step.  Writing the reduced tail
as `u n / v n` in lowest terms, the step is the division-free cocycle

* `w n + v n = a n * u n`      (raw next numerator),
* `w n = hc n * u (n + 1)`     (reduced next numerator),
* `a n * v n = hc n * v (n + 1)` (reduced next denominator).

`DynamicCancellation` already supplies the primitive identities
`Nat.gcd (w n) (a n * v n) = Nat.gcd (w n) (a n ^ 2)` and
`Nat.Coprime (u n) (w n)`; the second gives `Nat.Coprime (u n) (u (n + 1))`
because `u (n + 1) ∣ w n`.

The chain proved here is:

1. `primitive_valuation_no_drop` — a prime power `p ^ l ∣ v n` cannot leave the
   reduced denominator while the *raw* numerator stays below `p ^ (l + 1)`.
   This is the only place where arbitrary cancellation is controlled: no bound
   on `hc n` is used anywhere.
2. `protectedPrimePower_persists` — the persistence of that prime power up to
   and including the first index at which `u` reaches a height `H` with
   `3 * H < 2 * p ^ (l + 1)`.
3. `odd_record_cut` — if `H` is an *odd* multiple of `p` above the running
   numerator maximum, the orbit can never reach `H` at all, provided every
   record-setting step rises by at most `2`.  The first crossing would have to
   be a record; `p ∣ v` kills the landing `u = H`, and the only other option
   `(H - 1, H + 1)` has both endpoints even, contradicting adjacent-numerator
   coprimality.
4. `recordRiseTwo_sylvesterNext_eventually` — the composed consumer.  The
   analytic *supply* of fresh odd large prime powers is an explicit hypothesis;
   see the module note at the end for exactly which bridges remain open.

Nothing in this module is conditional on a bound for the cancellation factors,
and no hypothesis is imposed at non-record steps.
-/

namespace ErdosProblems.Erdos243

/-! ## 1. The valuation-loss threshold

r07 Lemma 1 / r08 Lemma 2.  Stated with `p ^ l ∣ v` rather than `p ^ l ‖ v`:
the divisibility form is strictly stronger, because `w < p ^ (l + 1)` is then
also below `p ^ (ν_p v + 1)`. -/



/-! ## 2. Persistence up to a first height crossing (r07 Lemma 2) -/



/-! ## 3. The running numerator maximum -/

/-- Running maximum `R n = max_{k ≤ n} u k` of a numerator sequence. -/
def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

theorem le_runningMax (u : ℕ → ℕ) {k n : ℕ} (h : k ≤ n) : u k ≤ runningMax u n := by
  induction n with
  | zero => have : k = 0 := by omega
            subst this; exact le_rfl
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hlt | hge
      · exact le_trans (ih (by omega)) (le_max_left _ _)
      · have : k = m + 1 := by omega
        subst this
        exact le_max_right _ _



/-! ## 4. The odd protected cut (r07 Lemma 3) -/



/-! ## 5. The prime-power trap (r07 Corollary 4) -/



/-! ## 6. Bounded numerator from a single fresh odd source -/



/-! ## 7. Composition to the Sylvester endpoint

The primitive centred error is `e n = v n - (a n - 1) * u n`, so that
`e n = u n - w n` as integers.  A vanishing centred error is absorbing under
the nearest-integer normalisation `2 * |e n| < u n`, and it pins the multiplier
exactly. -/







/-! ## 8. The composed consumer -/



/-!
## Remaining analytic bridges

`recordRiseTwo_sylvesterNext_eventually` is fully proved from its hypotheses.
Two of those hypotheses are analytic inputs that this module does **not**
derive:

* `hsupply` — the fresh odd large prime-power supply (r07 Lemmas 5-7, r08
  Lemma 4).  Its ordinary proof needs `log R n = o n`, `log (a n) = κ 2 ^ n`
  with `κ > 0`, the factorial separation `a j > (3 * R (j+1))!`, and the
  cumulative-lcm freshness budget of `CumulativeLcmTransfer`.  This is the same
  shape of input that the corpus row `bounded_lcm_negative_arithmetic_core`
  records as an open prime-supply bridge.
* `hvanish` — the normalised vanishing `∀ K, eventually K * |e n| < u n`, i.e.
  `E n / C n → 0` in primitive coordinates.  It is the same hypothesis carried
  by `boundedNegativePart_sylvesterNext_eventually` in `ReciprocalTailRigidity`.

`hcentre` (the nearest-integer normalisation `2 * |e n| < u n`) is a
consequence of `hvanish` at `K = 2` and is kept separate only to keep the
absorption step free of an index maximisation.

-- OPEN: the quantitative record-excess obligation (r07 Theorem 8).  Statement:
-- given the hypotheses of `numerator_bounded_of_oddPrimePower` minus `hrec`,
-- with `L = p ^ (l + 1) / 2` and `τ` the first index `≥ s` with `L ≤ u τ`,
--   `p ^ l / 6 - 2 ≤ ∑ n in recordSteps s τ, (u (n + 1) - u n - 2)`
-- where `recordSteps s τ = {n | s ≤ n < τ ∧ runningMax u n < u (n + 1)}`.
-- Not formalised here: it needs a counting argument over the odd multiples of
-- `p` in `(runningMax u s, L]` together with the per-jump capacity bound
-- `⌊(d - 1) / 2⌋` for a coprime pair at distance `d`, which is a separate
-- finite-combinatorics development.

-- CHECKED, NEGATIVE: the wave-1 suggestion that the open prime supply of
-- `no_boundedNegative_lcmState_of_oldPrimeSupply` (`LcmCriticalBoundary.lean`)
-- closes from `CumulativeLcmTransfer` by an index-shift wrapper alone does not
-- hold against the actual Lean statements.  That theorem needs
-- `Nat.Prime (m i)` and `B < m i` for every `i ≥ N`, with `m i ∣ D t` for all
-- `t > i`.  `CumulativeLcmTransfer` supplies the multiplier facts
-- `digit_dvd_cumulativeDigitLcm_of_lt` (old-divisor persistence) and
-- `lcmFresh_pairwiseCoprime` (pairwise coprimality *at fresh indices*), plus a
-- density-one freshness budget.  Two gaps survive an index shift: the
-- multipliers `a i` are not prime and nothing in the corpus extracts from them
-- a prime factor exceeding `B` (that extraction is exactly r07 Lemma 6-7, an
-- analytic growth input); and reindexing to a fresh subsequence breaks
-- `hmOld`, whose divisibility is keyed to the same index as the orbit step.
-- So no wrapper was added.
-/

end ErdosProblems.Erdos243


