-- Prove2me | solution 1 for ErdosProblems.Erdos269.qsmul_trueNormalizedState_eq_height_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:07:17.517798+00:00
-- url     : https://prove2.me/submissions/0730fd89-08dd-486c-8971-84c0ad66fcce

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
import Theorems.Thm_ErdosProblems_Erdos269_heightNormalizer235_mul_windowMass_eq_int
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





/-! ## The lattice witness, made explicit -/
end ErdosProblems.Erdos269

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos269 in
theorem solution
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ))
    {a : ℕ} (ha : 1 ≤ a) :
    ∃ z : ℤ,
      (q : ℝ) * trueNormalizedState a
        = ((heightNormalizer235 a : ℕ) : ℝ) * (p : ℝ) - (q : ℝ) * (z : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, a = 1 + m := ⟨a - 1, by omega⟩
  have hsplit := dyadicShellTsumTailR235_eq_range_add 1 m
  set prefQ : ℚ := dyadicSmoothWindowMassQ235 1 m with hprefQ
  have hprefR : (∑ i ∈ Finset.range m, dyadicShellMassR235 (1 + i)) = (prefQ : ℝ) := by
    simp only [hprefQ, dyadicSmoothWindowMassQ235, dyadicShellMassR235, Rat.cast_sum]
  obtain ⟨z, hz⟩ := heightNormalizer235_mul_windowMass_eq_int 1 m
  have hnorm : trueNormalizedState (1 + m)
      = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * dyadicShellTsumTailR235 (1 + m) := by
    unfold trueNormalizedState dyadicNormalizedTailStateR235
    have h2 : ((threePrimeHeight 2 3 5 (2 ^ (1 + m)) : ℕ) : ℝ)
        = 2 * ((heightNormalizer235 (1 + m) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ))
        (two_mul_heightNormalizer235 (1 + m) (by omega)).symm
    rw [h2]
    ring
  have htail : dyadicShellTsumTailR235 (1 + m) = (p : ℝ) / (q : ℝ) - (prefQ : ℝ) := by
    have := hsplit
    rw [hprefR, hval] at this
    linarith
  have hzR : ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (prefQ : ℝ) = ((z : ℕ) : ℝ) := by
    exact_mod_cast congrArg (fun r : ℚ => (r : ℝ)) hz
  have hqne : (q : ℝ) ≠ 0 := by
    exact_mod_cast hq.ne'
  have hqp : (q : ℝ) * ((p : ℝ) / (q : ℝ)) = (p : ℝ) := by field_simp
  refine ⟨(z : ℤ), ?_⟩
  rw [hnorm, htail]
  push_cast
  calc (q : ℝ) * (((heightNormalizer235 (1 + m) : ℕ) : ℝ)
          * ((p : ℝ) / (q : ℝ) - (prefQ : ℝ)))
      = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * ((q : ℝ) * ((p : ℝ) / (q : ℝ)))
          - (q : ℝ) * (((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (prefQ : ℝ)) := by ring
    _ = ((heightNormalizer235 (1 + m) : ℕ) : ℝ) * (p : ℝ) - (q : ℝ) * ((z : ℕ) : ℝ) := by
          rw [hqp, hzR]
