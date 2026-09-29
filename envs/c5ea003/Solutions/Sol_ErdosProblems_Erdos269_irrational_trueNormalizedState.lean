-- Prove2me | solution 1 for ErdosProblems.Erdos269.irrational_trueNormalizedState
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:48:03.40044+00:00
-- url     : https://prove2.me/submissions/679aa469-cf83-44b5-a4bd-1910edbf03da

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
import Theorems.Thm_ErdosProblems_Erdos269_threePrimeHeight235_cast_pos
import Theorems.Thm_ErdosProblems_Erdos269_dyadicShellTsumTailR235_eq_range_add
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

namespace ErdosProblems.Erdos269
open scoped BigOperators

/-! ## The real window identity for the genuine normalized state -/







/-! ## Irrationality transfers from the value to every normalized state -/

theorem irrational_dyadicShellTsumTailR235_of_one
    (h : Irrational (dyadicShellTsumTailR235 1)) (a : ℕ) (ha : 1 ≤ a) :
    Irrational (dyadicShellTsumTailR235 a) := by
  obtain ⟨m, rfl⟩ : ∃ m, a = 1 + m := ⟨a - 1, by omega⟩
  have hsplit := dyadicShellTsumTailR235_eq_range_add 1 m
  have hprefR : (∑ i ∈ Finset.range m, dyadicShellMassR235 (1 + i))
      = ((dyadicSmoothWindowMassQ235 1 m : ℚ) : ℝ) := by
    simp only [dyadicSmoothWindowMassQ235, dyadicShellMassR235, Rat.cast_sum]
  rw [hprefR] at hsplit
  have hrw : dyadicShellTsumTailR235 (1 + m)
      = dyadicShellTsumTailR235 1 - ((dyadicSmoothWindowMassQ235 1 m : ℚ) : ℝ) := by
    linarith
  rw [hrw]
  exact h.sub_ratCast _
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    (h : Irrational (dyadicShellTsumTailR235 1)) (a : ℕ) (ha : 1 ≤ a) :
    Irrational (trueNormalizedState a) := by
  set q : ℚ := (threePrimeHeight 2 3 5 (2 ^ a) : ℚ) / 2 with hq
  have hqne : q ≠ 0 := by
    rw [hq]
    have hpos : (0 : ℝ) < (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) :=
      threePrimeHeight235_cast_pos _
    have hne : (threePrimeHeight 2 3 5 (2 ^ a) : ℚ) ≠ 0 := by
      have : threePrimeHeight 2 3 5 (2 ^ a) ≠ 0 := by
        intro hz
        rw [hz] at hpos
        simp at hpos
      exact_mod_cast this
    simpa using hne
  have hstate : trueNormalizedState a = (q : ℝ) * dyadicShellTsumTailR235 a := by
    unfold trueNormalizedState dyadicNormalizedTailStateR235
    rw [hq]
    push_cast
    ring
  rw [hstate]
  exact (irrational_dyadicShellTsumTailR235_of_one h a ha).ratCast_mul hqne
