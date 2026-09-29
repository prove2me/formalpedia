-- Prove2me | solution 1 for ErdosProblems.Erdos269.smooth_dvd_heightNormalizer235
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:09:59.142789+00:00
-- url     : https://prove2.me/submissions/7e3a370e-d0c6-41cf-bee1-fe1a98d2ec3d

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
import Theorems.Thm_ErdosProblems_Erdos269_two_mul_heightNormalizer235
import Theorems.Thm_ErdosProblems_Erdos269_smooth3Val_dvd_threePrimeHeight_of_le
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
# Erdős #269: the rationality-to-carry bridge, closed

The paper's Problem `prob:bridge269` ("actual rationality-to-carry
identification") asks: starting from the `{2,3,5}` running-LCM series and a
reduced denominator `D = D_sm · B` with `D_sm` `30`-smooth and `gcd(B,30) = 1`,
prove with a stated onset `a ≥ a_D` that the literal radix word
`β_a = dyadicBlockBase235 a`, the literal digit `m_a = dyadicOrderedBlockDigit235 a`
and the literal normalized tail `T_a = trueNormalizedState a` give positive
integral carries `c_a = D T_a` with `c_(a+1) = β_a c_a - D m_a`, an explicit
bound, and `D_sm ∣ c_a`; and that the reduced carry `d_a = c_a / D_sm` obeys
`d_(a+1) = β_a d_a - B m_a` with `0 < d_a ≤ K(B, a)`.

This module proves exactly that, with `K(B, a) = B · 90 (a+1)^2` (the width of
`NormalizedStateWidth`) and onset `a_D = α + 1 + 2β + 3γ` for
`D_sm = 2^α 3^β 5^γ`.  The pieces:

* `exists_smooth_coprime_split` — every positive integer is `2^α 3^β 5^γ · B`
  with `gcd(B, 30) = 1`;
* `smooth_dvd_heightNormalizer235` — the half height `H(2^a)/2` absorbs
  `2^α 3^β 5^γ` once `a ≥ α + 1 + 2β + 3γ`;
* `qsmul_trueNormalizedState_eq_height_mul_sub` — the all-scale lattice with
  its explicit witness `q X_a = (H(2^a)/2) p - q z_a`, so the carry is
  congruent to `(H(2^a)/2) p` modulo `q` and the smooth part divides it;
* `latticeCarry` and its recurrence, positivity and width, all inherited from
  the true state through the integer cast;
* `reducedLatticeCarry` — the quotient by the smooth part, with the reduced
  recurrence and the bound `0 < d_a ≤ B · 90 (a+1)^2` from the onset on.

The consumer `no_positive_reducedCarry_of_cofinalLocalWindowEscape` of
`RestrictedFloorSum` was stated for carries defined at every index; the
onset-aware form `no_positive_reducedCarry_of_cofinalLocalWindowEscape_onset`
proved here uses the producer's own `∀ lo₀ ∃ lo ≥ lo₀` clause to start the
window past the onset.

## Consequence

`irrational_of_cofinalLocalWindowEscape`: the paper's Problem `prob:producer`
(9.5), i.e. `CofinalLocalWindowEscape` for the actual radix word, the actual
ordered digit and the short bound `B · 90 (n+1)^2`, implies that
`Σ_{h ≥ 2} 1/H(h)` is irrational, hence (`irrational_value_of_cofinalLocalWindowEscape`)
that the Erdős #269 value `Σ_{h ≥ 1} 1/H(h)` is irrational.  The generic
extinction theorem is thereby a theorem about the actual series: the only
unproved input is the cofinal local-window escape itself.

## Claim ceiling

`CofinalLocalWindowEscape` is a named `Prop`, not a theorem.  Nothing here
proves it, and **Erdős #269 remains open**.  What is closed is the bridge: a
rational value forces, from an explicit onset, a positive reduced integral
carry of the exact shape the residue consumer refutes, with every object the
literal one from the series.
-/

namespace ErdosProblems.Erdos269
open scoped BigOperators

/-! ## Onset-aware window identity and consumer -/





/-! ## Splitting a denominator into its `30`-smooth and rough parts -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution {α β γ a : ℕ}
    (ha : α + 1 + 2 * β + 3 * γ ≤ a) :
    2 ^ α * 3 ^ β * 5 ^ γ ∣ heightNormalizer235 a := by
  have h1 : 1 ≤ a := by omega
  have hle : smooth3Val 2 3 5 (α + 1) β γ ≤ 2 ^ a := by
    unfold smooth3Val
    calc 2 ^ (α + 1) * 3 ^ β * 5 ^ γ
        ≤ 2 ^ (α + 1) * 4 ^ β * 8 ^ γ := by gcongr <;> norm_num
      _ = 2 ^ (α + 1 + 2 * β + 3 * γ) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, show (8 : ℕ) = 2 ^ 3 by norm_num,
            ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hdvd := smooth3Val_dvd_threePrimeHeight_of_le
    (p := 2) (q := 3) (r := 5) (by norm_num) (by norm_num) (by norm_num) hle
  rw [← two_mul_heightNormalizer235 a h1] at hdvd
  have hsv : smooth3Val 2 3 5 (α + 1) β γ = 2 * (2 ^ α * 3 ^ β * 5 ^ γ) := by
    unfold smooth3Val
    ring
  rw [hsv] at hdvd
  exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hdvd
