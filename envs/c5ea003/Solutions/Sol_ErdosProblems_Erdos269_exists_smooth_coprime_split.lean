-- Prove2me | solution 1 for ErdosProblems.Erdos269.exists_smooth_coprime_split
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:37:54.352588+00:00
-- url     : https://prove2.me/submissions/1a82f1c4-ea16-4e20-8489-7f50cc2c53d9

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
theorem solution (q : ℕ) (hq : 0 < q) :
    ∃ α β γ B : ℕ,
      q = 2 ^ α * 3 ^ β * 5 ^ γ * B ∧ 0 < B ∧ Nat.Coprime B 30 := by
  obtain ⟨α, q₁, h2, rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hq.ne' 2 (by norm_num)
  have hq₁ : q₁ ≠ 0 := by
    rintro rfl
    simp at hq
  obtain ⟨β, q₂, h3, rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hq₁ 3 (by norm_num)
  have hq₂ : q₂ ≠ 0 := by
    rintro rfl
    simp at hq₁
  obtain ⟨γ, B, h5, rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hq₂ 5 (by norm_num)
  have hB : B ≠ 0 := by
    rintro rfl
    simp at hq₂
  have h2B : ¬ 2 ∣ B := fun h =>
    h2 (Dvd.dvd.mul_left (Dvd.dvd.mul_left h _) _)
  have h3B : ¬ 3 ∣ B := fun h => h3 (Dvd.dvd.mul_left h _)
  have hc2 : Nat.Coprime B 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2B).symm
  have hc3 : Nat.Coprime B 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3B).symm
  have hc5 : Nat.Coprime B 5 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5).symm
  refine ⟨α, β, γ, B, by ring, Nat.pos_of_ne_zero hB, ?_⟩
  have h30 : (30 : ℕ) = 2 * 3 * 5 := by norm_num
  rw [h30]
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right hc2 hc3) hc5
