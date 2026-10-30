-- Prove2me | solution 1 for AnalyticCombinatorics.Ch7.SingularityApp.ForestsNS.rootedForest_over_factorial_isEquivalent_exp_add
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T18:15:30.092996+00:00
-- url     : https://prove2.me/submissions/35d3fb70-02db-4203-a3cb-48bbc831fd6e

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TreeFunction
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_Forests
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Cayley tree-function coefficient asymptotic

The tree function

`T(z) = sum_{n >= 1} n^(n-1) z^n / n!`

has coefficients given exactly by Cayley's rooted labelled tree count.  This
file proves the coefficient asymptotic directly from Stirling's formula:

`n^(n-1) / n! ~ exp n / (sqrt (2*pi) * n^(3/2))`.

The exponent is `3/2`, not `5/2`: Stirling contributes
`1 / sqrt(2*pi*n)` and the quotient `n^(n-1) / n^n` contributes one more
factor `1/n`.
-/

open Filter Asymptotics
open scoped Topology

namespace AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

lemma factorial_isEquivalent_treeStirlingScale :
    (fun n : ℕ => (n.factorial : ℝ)) ~[atTop]
      (fun n : ℕ => treeStirlingScale n) := by
  simpa [treeStirlingScale] using Stirling.factorial_isEquivalent_stirling

lemma cayleyRootedTree_cast (n : ℕ) :
    (cayleyRootedTree n : ℝ) = (n : ℝ) ^ (n - 1) := by
  simp [cayleyRootedTree]

lemma treeFunctionCoeff_isEquivalent_treeStirlingScale :
    (fun n : ℕ => treeFunctionCoeff n) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ (n - 1) / treeStirlingScale n) := by
  have hbridge :
      (fun n : ℕ => treeFunctionCoeff n) =ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) ^ (n - 1) / (n.factorial : ℝ)) :=
    Eventually.of_forall fun n => by
      simp [treeFunctionCoeff, cayleyRootedTree_cast]
  have hdiv :
      (fun n : ℕ => (n : ℝ) ^ (n - 1) / (n.factorial : ℝ)) ~[atTop]
        (fun n : ℕ => (n : ℝ) ^ (n - 1) / treeStirlingScale n) := by
    simpa only [Pi.div_apply] using
      (Asymptotics.IsEquivalent.refl
        (l := atTop) (u := fun n : ℕ => (n : ℝ) ^ (n - 1))).div
          factorial_isEquivalent_treeStirlingScale
  exact hbridge.trans_isEquivalent hdiv

lemma rpow_three_halves_mul_nat_real (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  nth_rw 2 [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnpos]
  norm_num

lemma sqrt_two_pi_mul_nat_eq_sqrt_two_pi_mul_rpow_real (n : ℕ) (hn : n ≠ 0) :
    Real.sqrt (2 * (n : ℝ) * Real.pi) * (n : ℝ) =
      Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)) := by
  rw [show 2 * (n : ℝ) * Real.pi = (2 * Real.pi) * (n : ℝ) by ring]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [mul_assoc, rpow_three_halves_mul_nat_real n hn]

lemma treeStirlingScale_simplified (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) ^ (n - 1) / treeStirlingScale n =
      (Real.exp 1) ^ n /
        (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ))) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hE : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have hnpow : (n : ℝ) ^ (n - 1) ≠ 0 := pow_ne_zero _ hnR
  have hEpow : (Real.exp 1) ^ n ≠ 0 := pow_ne_zero _ hE
  have hsqrt : Real.sqrt (2 * (n : ℝ) * Real.pi) ≠ 0 := by positivity
  have hpow :
      (n : ℝ) ^ n = (n : ℝ) ^ (n - 1) * (n : ℝ) := by
    conv_lhs => rw [← Nat.sub_one_add_one hn]
    rw [pow_succ]
    rw [Nat.sub_one_add_one hn]
  unfold treeStirlingScale
  rw [div_pow, hpow]
  rw [show
      (n : ℝ) ^ (n - 1) /
          (Real.sqrt (2 * (n : ℝ) * Real.pi) *
            (((n : ℝ) ^ (n - 1) * (n : ℝ)) / (Real.exp 1) ^ n)) =
        (Real.exp 1) ^ n /
          (Real.sqrt (2 * (n : ℝ) * Real.pi) * (n : ℝ)) by
        field_simp [hnpow, hEpow, hnR, hsqrt]]
  rw [sqrt_two_pi_mul_nat_eq_sqrt_two_pi_mul_rpow_real n hn]

theorem treeFunctionCoeff_isEquivalent_exp_one_pow :
    (fun n : ℕ => treeFunctionCoeff n) ~[atTop]
      (fun n : ℕ =>
        (Real.exp 1) ^ n /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  exact treeFunctionCoeff_isEquivalent_treeStirlingScale.trans_eventuallyEq
    ((eventually_ne_atTop 0).mono fun n hn => by
      dsimp
      rw [treeStirlingScale_simplified n hn])

lemma exp_one_pow_nat_eq_exp_nat (n : ℕ) :
    (Real.exp 1) ^ n = Real.exp (n : ℝ) := by
  simp [← Real.exp_nat_mul]

/--
The tree-function coefficient asymptotic.  Since
`treeFunctionCoeff n = n^(n-1)/n!`, Stirling gives the leading term
`exp n / (sqrt(2*pi) * n^(3/2))`.
-/
theorem treeFunctionCoeff_isEquivalent :
    (fun n : ℕ => treeFunctionCoeff n) ~[atTop]
      (fun n : ℕ =>
        Real.exp (n : ℝ) /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  exact treeFunctionCoeff_isEquivalent_exp_one_pow.trans_eventuallyEq
    (Eventually.of_forall fun n => by
      dsimp
      rw [exp_one_pow_nat_eq_exp_nat n])

end AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

/-!
# Rooted labelled forests

A rooted labelled forest on `[n]` is a finite SET of rooted labelled Cayley
trees.  Its EGF is `F(z) = exp(T(z))`, where `T = z exp T` is the tree
function.  The classical Cayley-Prüfer count is

`rootedForest n = (n + 1)^(n - 1)`.

Equivalently, the forest EGF coefficient is the next tree-function
coefficient:

`rootedForest n / n! = treeFunctionCoeff (n + 1)`.

The asymptotic therefore follows from the tree-function Stirling asymptotic,
with the shift contributing the extra factor `exp 1`.
-/

open Filter Asymptotics
open scoped Topology

namespace AnalyticCombinatorics.Ch7.SingularityApp.ForestsNS

lemma rootedForestCoeff_eq_treeFunctionCoeff_succ (n : ℕ) :
    rootedForestCoeff n =
      AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff (n + 1) := by
  by_cases hn : n = 0
  · subst n
    norm_num [rootedForestCoeff, rootedForest,
      AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff,
      AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.cayleyRootedTree]
  · have hnp1R : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hpow :
        ((n + 1 : ℕ) : ℝ) ^ n =
          ((n + 1 : ℕ) : ℝ) ^ (n - 1) * ((n + 1 : ℕ) : ℝ) := by
      conv_lhs => rw [← Nat.sub_one_add_one hn]
      rw [pow_succ]
      rw [Nat.sub_one_add_one hn]
    unfold rootedForestCoeff rootedForest
    unfold AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff
    unfold AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.cayleyRootedTree
    rw [show n + 1 - 1 = n by omega]
    rw [show (n + 1).factorial = (n + 1) * n.factorial by
      exact Nat.factorial_succ n]
    norm_num [Nat.cast_mul]
    have hpow' :
        ((n : ℝ) + 1) ^ n =
          ((n : ℝ) + 1) ^ (n - 1) * ((n : ℝ) + 1) := by
      simpa using hpow
    rw [hpow']
    field_simp [hnp1R]

lemma natCast_succ_isEquivalent_self :
    (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) ~[atTop]
      (fun n : ℕ => (n : ℝ)) := by
  have hbase :
      (fun n : ℕ => (n : ℝ)) ~[atTop]
        (fun n : ℕ => (n : ℝ) + 1) := by
    apply isEquivalent_of_tendsto_one
    simpa using tendsto_natCast_div_add_atTop (1 : ℝ)
  have hsucc :
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ))) =ᶠ[atTop]
        (fun n : ℕ => (n : ℝ) + 1) :=
    Eventually.of_forall fun n => by norm_num
  exact hsucc.trans_isEquivalent hbase.symm

lemma natCast_succ_rpow_three_halves_isEquivalent_self :
    (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))) ~[atTop]
      (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))) := by
  exact natCast_succ_isEquivalent_self.rpow (by intro n; positivity)

lemma forest_shifted_tree_scale_isEquivalent :
    (fun n : ℕ =>
        Real.exp (((n + 1 : ℕ) : ℝ)) /
          (Real.sqrt (2 * Real.pi) * (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)))) ~[atTop]
      (fun n : ℕ =>
        Real.exp 1 * Real.exp (n : ℝ) /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  have hden :
      (fun n : ℕ =>
          Real.sqrt (2 * Real.pi) * (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ))) ~[atTop]
        (fun n : ℕ =>
          Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ))) := by
    simpa only [Pi.mul_apply] using
      (Asymptotics.IsEquivalent.refl
        (l := atTop) (u := fun _ : ℕ => Real.sqrt (2 * Real.pi))).mul
        natCast_succ_rpow_three_halves_isEquivalent_self
  have hraw :
      (fun n : ℕ =>
          Real.exp (((n + 1 : ℕ) : ℝ)) /
            (Real.sqrt (2 * Real.pi) * (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)))) ~[atTop]
        (fun n : ℕ =>
          Real.exp (((n + 1 : ℕ) : ℝ)) /
            (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
    simpa only [Pi.div_apply] using
      (Asymptotics.IsEquivalent.refl
        (l := atTop) (u := fun n : ℕ => Real.exp (((n + 1 : ℕ) : ℝ)))).div hden
  exact hraw.trans_eventuallyEq (Eventually.of_forall fun n => by
    dsimp
    rw [show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by norm_num]
    rw [Real.exp_add]
    ring)

theorem rootedForestCoeff_isEquivalent :
    (fun n : ℕ => rootedForestCoeff n) ~[atTop]
      (fun n : ℕ =>
        Real.exp 1 * Real.exp (n : ℝ) /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  have hbridge :
      (fun n : ℕ => rootedForestCoeff n) =ᶠ[atTop]
        (fun n : ℕ =>
          AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff (n + 1)) :=
    Eventually.of_forall rootedForestCoeff_eq_treeFunctionCoeff_succ
  have htree :=
    Asymptotics.IsEquivalent.comp_tendsto
      AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff_isEquivalent
      (tendsto_add_atTop_nat 1)
  have htree' :
      (fun n : ℕ =>
          AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS.treeFunctionCoeff (n + 1)) ~[atTop]
        (fun n : ℕ =>
          Real.exp (((n + 1 : ℕ) : ℝ)) /
            (Real.sqrt (2 * Real.pi) * (((n + 1 : ℕ) : ℝ) ^ (3 / 2 : ℝ)))) := by
    simpa [Function.comp_def] using htree
  exact hbridge.trans_isEquivalent
    (htree'.trans forest_shifted_tree_scale_isEquivalent)

theorem rootedForest_over_factorial_isEquivalent :
    (fun n : ℕ => (rootedForest n : ℝ) / n.factorial) ~[atTop]
      (fun n : ℕ =>
        Real.exp 1 * Real.exp (n : ℝ) /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  simpa [rootedForestCoeff] using rootedForestCoeff_isEquivalent

lemma forest_asymptotic_exp_add_scale_eq (n : ℕ) :
    Real.exp 1 * Real.exp (n : ℝ) /
        (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ))) =
      Real.exp ((n : ℝ) + 1) /
        (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ))) := by
  rw [Real.exp_add]
  ring

end AnalyticCombinatorics.Ch7.SingularityApp.ForestsNS

open AnalyticCombinatorics AnalyticCombinatorics.Ch7 AnalyticCombinatorics.Ch7.SingularityApp AnalyticCombinatorics.Ch7.SingularityApp.ForestsNS
open Filter Asymptotics
open scoped Topology
theorem solution :
    (fun n : ℕ => (rootedForest n : ℝ) / n.factorial) ~[atTop]
      (fun n : ℕ =>
        Real.exp ((n : ℝ) + 1) /
          (Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)))) := by
  exact rootedForest_over_factorial_isEquivalent.trans_eventuallyEq
    (Eventually.of_forall fun n => by
      dsimp
      rw [forest_asymptotic_exp_add_scale_eq n])
