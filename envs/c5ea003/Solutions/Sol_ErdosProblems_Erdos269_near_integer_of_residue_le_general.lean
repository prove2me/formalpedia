-- Prove2me | solution 1 for ErdosProblems.Erdos269.near_integer_of_residue_le_general
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:51:59.765618+00:00
-- url     : https://prove2.me/submissions/5a47398e-595b-4caa-8f5a-35d8d9f69f43

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
import Theorems.Thm_ErdosProblems_Erdos269_trueNormalizedState_le_quadratic
import Theorems.Thm_ErdosProblems_Erdos269_trueNormalizedState_pos
import Theorems.Thm_ErdosProblems_Erdos269_leastPositiveResidue_modEq
import Theorems.Thm_ErdosProblems_Erdos269_leastPositiveResidue_pos_le
import Theorems.Thm_ErdosProblems_Erdos269_trueNormalizedState_window
import Theorems.Thm_ErdosProblems_Erdos269_two_pow_le_windowBase235
import Theorems.Thm_ErdosProblems_Erdos269_windowBase235_pos
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
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    (B lo len K : ℕ) (hB : 0 < B)
    (hKle : B * bridgeWidth (lo + len) ≤ K)
    (hres : leastPositiveResidue
        (Int.natAbs (windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len))
        (-((B : ℤ) * windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
             (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len))
      ≤ K) :
    ∃ k : ℤ, |(B : ℝ) * trueNormalizedState lo - (k : ℝ)|
      ≤ ((K : ℕ) : ℝ) / 2 ^ len := by
  classical
  set W : ℤ := windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len with hW
  set F : ℤ := windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
      (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len with hF
  have hWpos : 0 < W := windowBase235_pos lo len
  have hWnat : ((Int.natAbs W : ℕ) : ℤ) = W := Int.natAbs_of_nonneg hWpos.le
  have hWnatpos : 0 < Int.natAbs W := Int.natAbs_pos.mpr hWpos.ne'
  set r : ℕ := leastPositiveResidue (Int.natAbs W) (-((B : ℤ) * F)) with hr
  obtain ⟨hrpos, hrle⟩ := leastPositiveResidue_pos_le hWnatpos (-((B : ℤ) * F))
  have hmod : Int.ModEq (Int.natAbs W) (r : ℤ) (-((B : ℤ) * F)) :=
    leastPositiveResidue_modEq hWnatpos _
  obtain ⟨t, ht⟩ : (W : ℤ) ∣ (-((B : ℤ) * F) - (r : ℤ)) := by
    have := Int.ModEq.dvd hmod
    rwa [hWnat] at this
  -- the real window identity
  have hwin := trueNormalizedState_window lo len
  rw [← hW, ← hF] at hwin
  set X : ℝ := trueNormalizedState lo with hX
  set Y : ℝ := trueNormalizedState (lo + len) with hY
  have htR : -((B : ℝ) * (F : ℝ)) - (r : ℝ) = (W : ℝ) * (t : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) ht
  have hFR : (F : ℝ) = (W : ℝ) * X - Y := by rw [hwin]; ring
  refine ⟨-t, ?_⟩
  have hkey : (W : ℝ) * ((B : ℝ) * X - ((-t : ℤ) : ℝ)) = (B : ℝ) * Y - (r : ℝ) := by
    rw [hFR] at htR
    push_cast
    push_cast at htR
    linarith
  -- bound the right-hand side by `K`
  have hYpos : 0 < Y := trueNormalizedState_pos _
  have hYle : Y ≤ 90 * ((lo + len + 1 : ℕ) : ℝ) ^ 2 :=
    trueNormalizedState_le_quadratic (lo + len)
  have hKR : ((B * bridgeWidth (lo + len) : ℕ) : ℝ)
      = (B : ℝ) * (90 * ((lo + len + 1 : ℕ) : ℝ) ^ 2) := by
    unfold bridgeWidth
    push_cast
    ring
  have hKcast : ((B * bridgeWidth (lo + len) : ℕ) : ℝ) ≤ ((K : ℕ) : ℝ) := by
    exact_mod_cast hKle
  have hBY : (B : ℝ) * Y ≤ ((K : ℕ) : ℝ) := by
    refine le_trans ?_ hKcast
    rw [hKR]
    exact mul_le_mul_of_nonneg_left hYle (by positivity)
  have hBYpos : 0 < (B : ℝ) * Y := by
    have : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
    positivity
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrpos
  have hrK : (r : ℝ) ≤ ((K : ℕ) : ℝ) := by exact_mod_cast hres
  have habs : |(B : ℝ) * Y - (r : ℝ)| ≤ ((K : ℕ) : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  -- divide by `W ≥ 2^len`
  have hWR : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hWpos
  have h2len : ((2 : ℝ) ^ len) ≤ (W : ℝ) := by
    have := two_pow_le_windowBase235 lo len
    rw [← hW] at this
    exact_mod_cast this
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ len := by positivity
  have habs2 : (W : ℝ) * |(B : ℝ) * X - ((-t : ℤ) : ℝ)| ≤ ((K : ℕ) : ℝ) := by
    calc (W : ℝ) * |(B : ℝ) * X - ((-t : ℤ) : ℝ)|
        = |(W : ℝ) * ((B : ℝ) * X - ((-t : ℤ) : ℝ))| := by
          rw [abs_mul, abs_of_pos hWR]
      _ = |(B : ℝ) * Y - (r : ℝ)| := by rw [hkey]
      _ ≤ ((K : ℕ) : ℝ) := habs
  have hnn : 0 ≤ |(B : ℝ) * X - ((-t : ℤ) : ℝ)| := abs_nonneg _
  rw [le_div_iff₀ h2pos]
  calc |(B : ℝ) * X - ((-t : ℤ) : ℝ)| * (2 : ℝ) ^ len
      ≤ |(B : ℝ) * X - ((-t : ℤ) : ℝ)| * (W : ℝ) :=
        mul_le_mul_of_nonneg_left h2len hnn
    _ = (W : ℝ) * |(B : ℝ) * X - ((-t : ℤ) : ℝ)| := by ring
    _ ≤ ((K : ℕ) : ℝ) := habs2
