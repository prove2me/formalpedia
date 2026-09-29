-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_near_integer_of_residue_le_general
-- name    : ErdosProblems.Erdos269.near_integer_of_residue_le_general
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T21:51:15.396742+00:00
-- url     : https://prove2.me/theorems/82fa0731-1be5-4c34-b5e7-e8f85de10a10
-- title:
--   Near integer of residue le general
-- statement:
--   If a local-window residue is no larger than a bound K that also covers the terminal state width, then B times the starting true state is within K/2^len of an integer.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/CofinalWindowEscapeEquivalence.lean#L176-L263
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_IntegralBranchExtinction
import Definitions.Def_ErdosProblems_Erdos269_RationalLatticeReduction
import Definitions.Def_ErdosProblems_Erdos269_RationalityCarryBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Erdős #269: the cofinal local-window escape producer is *equivalent* to the target

`RationalityCarryBridge` closes the rationality-to-carry bridge and derives

  `ActualCofinalLocalWindowEscape → Irrational (Σ_{h ∈ ⟨2,3,5⟩} 1/H(h))`.

The producer was therefore recorded as a *strictly stronger, target-deciding*
open route.  This module proves the **converse**, unconditionally:

  `Irrational (Σ_{h ∈ ⟨2,3,5⟩} 1/H(h)) → ActualCofinalLocalWindowEscape`,

so the two are exactly equivalent (`actualCofinalLocalWindowEscape_iff`,
`actualCofinalLocalWindowEscape_iff_irrational_value`).

## What this proves and what it does not

It **proves** an exact equivalence of two propositions.  It does **not** prove
either of them.  **Erdős #269 remains open.**  The mathematical content is a
*no-go for the producer as a reduction*: `ActualCofinalLocalWindowEscape` is
not a weaker, more tractable statement one could hope to attack by
window/anti-concentration arguments and thereby obtain irrationality; proving
it is literally proving Erdős #269.  Any future effort spent on the producer
must be justified as an attack on the target itself.

## The mechanism

Let `X_a = trueNormalizedState a` be the genuine half-height normalized tail,
`b` the actual radix word and `m` the actual ordered digit, so
`X_{a+1} = b_a X_a - m_a`, `0 < X_a ≤ 90 (a+1)^2`.  Unrolling across a window
`[lo, lo+len)` gives, over the reals,

  `X_{lo+len} = W X_lo - F`,   `W = windowBase b lo len`,  `F = windowForcing b m lo len`.

If the least positive residue `r` of `-(B F)` modulo `W` satisfies `r ≤ K` with
`K = B · 90 (lo+len+1)^2`, then writing `r + B F = W k'` and substituting
`F = W X_lo - X_{lo+len}` yields the *exact* identity

  `W · (B X_lo - k) = B X_{lo+len} - r`,  `k = -k'`,

and since `0 < B X_{lo+len} ≤ K` and `0 < r ≤ K`, we get
`dist(B X_lo, ℤ) ≤ K / W ≤ K / 2^len` (`near_integer_of_residue_le`).

That is the whole story: the residue can only stay short if `B X_lo` is
exponentially well approximated by an integer at *every* window length.  As
`K` grows quadratically in `len` and `W ≥ 2^len` grows exponentially, an
irrational `B X_lo` forces the residue to escape at some finite `len`
(`cofinalLocalWindowEscape_of_irrational`), and conversely a short residue at
every window is exactly the rational/integral-carry branch the bridge already
consumes.

The exponential-beats-quadratic step is kept elementary and
`Nat`-only (`exists_pow_gt_quadratic`, via `n < 2^n` at window length `3n`),
so nothing here depends on limit machinery.
-/


open scoped BigOperators

/-! ## The real window identity for the genuine normalized state -/







/-! ## Irrationality transfers from the value to every normalized state -/





/-! ## Exponential beats quadratic, elementarily -/



/-! ## The core inequality: a short residue pins `B X_lo` near an integer -/

open ErdosProblems.Erdos269

theorem ErdosProblems.Erdos269.near_integer_of_residue_le_general
    (B lo len K : ℕ) (hB : 0 < B)
    (hKle : B * bridgeWidth (lo + len) ≤ K)
    (hres : leastPositiveResidue
        (Int.natAbs (windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len))
        (-((B : ℤ) * windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
             (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len))
      ≤ K) :
    ∃ k : ℤ, |(B : ℝ) * trueNormalizedState lo - (k : ℝ)|
      ≤ ((K : ℕ) : ℝ) / 2 ^ len := by sorry
