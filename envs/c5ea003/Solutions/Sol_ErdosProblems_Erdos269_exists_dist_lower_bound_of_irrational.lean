-- Prove2me | solution 1 for ErdosProblems.Erdos269.exists_dist_lower_bound_of_irrational
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:46:54.506286+00:00
-- url     : https://prove2.me/submissions/d4671d6d-89bf-4a90-9012-d91c950391d6

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

namespace ErdosProblems.Erdos269
open scoped BigOperators

/-! ## The real window identity for the genuine normalized state -/







/-! ## Irrationality transfers from the value to every normalized state -/





/-! ## Exponential beats quadratic, elementarily -/



/-! ## The core inequality: a short residue pins `B X_lo` near an integer -/



/-! ## The converse of the bridge -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution {y : ℝ} (hy : Irrational y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℤ, δ ≤ |y - (k : ℝ)| := by
  have hfr0 : Int.fract y ≠ 0 := by
    intro h0
    have hyz : y = ((⌊y⌋ : ℤ) : ℝ) := by
      have hfa := Int.floor_add_fract y
      rw [h0] at hfa
      linarith
    exact hy.ne_int ⌊y⌋ hyz
  have hfrpos : 0 < Int.fract y := lt_of_le_of_ne (Int.fract_nonneg y) (Ne.symm hfr0)
  have hfrlt : Int.fract y < 1 := Int.fract_lt_one y
  refine ⟨min (Int.fract y) (1 - Int.fract y), lt_min hfrpos (by linarith), ?_⟩
  intro k
  have hfa := Int.floor_add_fract y
  rcases le_or_gt k ⌊y⌋ with hk | hk
  · have hkc : ((k : ℤ) : ℝ) ≤ ((⌊y⌋ : ℤ) : ℝ) := by exact_mod_cast hk
    have h1 : Int.fract y ≤ y - (k : ℝ) := by linarith
    exact le_trans (le_trans (min_le_left _ _) h1) (le_abs_self _)
  · have hk' : ⌊y⌋ + 1 ≤ k := by omega
    have hkc : ((⌊y⌋ : ℤ) : ℝ) + 1 ≤ ((k : ℤ) : ℝ) := by exact_mod_cast hk'
    have h1 : 1 - Int.fract y ≤ (k : ℝ) - y := by linarith
    have h3 : min (Int.fract y) (1 - Int.fract y) ≤ |(k : ℝ) - y| :=
      le_trans (le_trans (min_le_right (Int.fract y) (1 - Int.fract y)) h1)
        (le_abs_self ((k : ℝ) - y))
    rwa [abs_sub_comm] at h3
