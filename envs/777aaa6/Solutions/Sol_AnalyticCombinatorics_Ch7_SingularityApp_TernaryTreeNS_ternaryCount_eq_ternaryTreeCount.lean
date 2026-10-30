-- Prove2me | solution 1 for AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS.ternaryCount_eq_ternaryTreeCount
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:13:22.079278+00:00
-- url     : https://prove2.me/submissions/208f11f3-eed1-41e6-a209-b7179231d395

import Definitions.Def_AnalyticCombinatorics_Ch1_Lagrange_ImplicitSeries
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeBasic
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTrees
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTreeRecurrence
import Theorems.Thm_AnalyticCombinatorics_Ch1_Lagrange_Residue_lagrange_inversion_divided
import Mathlib
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
section
/-!
# Implicit formal power series

This file constructs, coefficient by coefficient, the unique formal power
series `T` with zero constant term satisfying `T = X * φ.subst T`.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch1.Lagrange

open PowerSeries

variable {R : Type*} [CommRing R]

namespace ImplicitSeries

lemma trunc_eq_of_coeff_eq {f g : R⟦X⟧} {n : ℕ}
    (h : ∀ i, i < n → coeff i f = coeff i g) :
    trunc n f = trunc n g := by
  ext i
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  split_ifs with hi
  · exact h i hi
  · rfl

lemma coeff_eq_coeff_trunc_pow (f : R⟦X⟧) (n d : ℕ) :
    coeff n (f ^ d) = coeff n (((trunc (n + 1) f : Polynomial R) : R⟦X⟧) ^ d) := by
  symm
  rw [← coeff_coe_trunc_of_lt (n := n) (m := n + 1)
    (f := (((trunc (n + 1) f : Polynomial R) : R⟦X⟧) ^ d)) (Nat.lt_succ_self n)]
  rw [PowerSeries.trunc_trunc_pow]
  rw [coeff_coe_trunc_of_lt (n := n) (m := n + 1) (f := f ^ d) (Nat.lt_succ_self n)]

lemma coeff_subst_eq_of_coeff_eq {f g : R⟦X⟧} (hf : PowerSeries.HasSubst f)
    (hg : PowerSeries.HasSubst g) (φ : R⟦X⟧) {n : ℕ}
    (h : ∀ i, i ≤ n → coeff i f = coeff i g) :
    coeff n (φ.subst f) = coeff n (φ.subst g) := by
  rw [PowerSeries.coeff_subst' hf φ n, PowerSeries.coeff_subst' hg φ n]
  apply finsum_congr
  intro d
  congr 1
  rw [coeff_eq_coeff_trunc_pow f n d, coeff_eq_coeff_trunc_pow g n d]
  congr 1
  exact congrArg (fun p : Polynomial R => ((p : R⟦X⟧) ^ d)) <|
    trunc_eq_of_coeff_eq (f := f) (g := g) (n := n + 1) fun i hi =>
      h i (Nat.le_of_lt_succ hi)

@[simp]
lemma coeff_partialSeries (a : ℕ → R) (n k : ℕ) :
    coeff k (partialSeries (R := R) a n) = if k < n then a k else 0 := by
  simp [partialSeries]

@[simp]
theorem coeff_implicitSeries (φ : R⟦X⟧) (n : ℕ) :
    coeff n (implicitSeries φ) = implicitCoeff φ n := by
  simp [implicitSeries]

@[simp]
theorem implicitCoeff_zero (φ : R⟦X⟧) :
    implicitCoeff φ 0 = 0 := by
  rw [implicitCoeff, Nat.strongRec_eq, implicitStep]

theorem implicitCoeff_succ (φ : R⟦X⟧) (n : ℕ) :
    implicitCoeff φ (n + 1) =
      coeff n (φ.subst (partialSeries (implicitCoeff φ) (n + 1))) := by
  rw [implicitCoeff, Nat.strongRec_eq, implicitStep]
  congr 2
  ext k
  by_cases hk : k < n + 1
  · simp only [coeff_partialSeries, hk, ↓reduceIte]
    rfl
  · simp only [coeff_partialSeries, hk, ↓reduceIte]

@[simp]
theorem constantCoeff_partialSeries_succ (a : ℕ → R) (n : ℕ) (h0 : a 0 = 0) :
    constantCoeff (partialSeries (R := R) a (n + 1)) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [h0]

@[simp]
theorem constantCoeff_implicitSeries (φ : R⟦X⟧) :
    constantCoeff (implicitSeries φ) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp

theorem hasSubst_partialSeries_implicitCoeff_succ (φ : R⟦X⟧) (n : ℕ) :
    PowerSeries.HasSubst (partialSeries (implicitCoeff φ) (n + 1)) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (constantCoeff_partialSeries_succ (R := R) (implicitCoeff φ) n (implicitCoeff_zero φ))

theorem implicitSeries_unique (φ T : R⟦X⟧)
    (hT : T = X * φ.subst T) (h0 : constantCoeff T = 0) :
    T = implicitSeries φ := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [coeff_implicitSeries, implicitCoeff_zero, coeff_zero_eq_constantCoeff_apply, h0]
      | succ n =>
          have hsubst : coeff n (φ.subst T) =
              coeff n (φ.subst (partialSeries (implicitCoeff φ) (n + 1))) := by
            apply coeff_subst_eq_of_coeff_eq
              (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
              (hasSubst_partialSeries_implicitCoeff_succ φ n)
            intro i hi
            have hlt : i < n + 1 := Nat.lt_succ_of_le hi
            have ih_i : coeff i T = coeff i (implicitSeries φ) := ih i hlt
            simp [coeff_implicitSeries, hlt, ih_i]
          have hcoeff := congrArg (coeff (n + 1)) hT
          rw [coeff_succ_X_mul] at hcoeff
          rw [coeff_implicitSeries, implicitCoeff_succ, ← hsubst, ← hcoeff]

section Sanity

@[simp]
theorem constantCoeff_geometricTail :
    constantCoeff (geometricTail (R := R)) = 0 := by
  rw [geometricTail, ← coeff_zero_eq_constantCoeff_apply]
  simp

end Sanity
end ImplicitSeries
end AnalyticCombinatorics.Ch1.Lagrange
end
end

section
/-!
# The triple-convolution recurrence for ternary trees

We establish the structural equivalence

`TernaryTreeOfSize (n+1) ≃ Σ p : TripleIndex n, (subtrees of sizes p.1, p.2.1, p.2.2)`

and derive a `Fintype` instance for `TernaryTreeOfSize n` together with the
triple-convolution recurrence for `ternaryCount`.
-/

namespace AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS

open scoped BigOperators

theorem ternaryCount_zero : ternaryCount 0 = 1 := by
  unfold ternaryCount
  rw [Fintype.card_eq_one_iff]
  exact ⟨⟨.leaf, rfl⟩, by rintro ⟨t, ht⟩; cases t with
    | leaf => rfl
    | node l m r => simp at ht⟩

theorem ternaryCount_succ (n : ℕ) :
    ternaryCount (n + 1) =
      ∑ p : TripleIndex n,
        ternaryCount p.val.1 *
        ternaryCount p.val.2.1 *
        ternaryCount p.val.2.2 := by
  unfold ternaryCount
  rw [Fintype.card_congr (succEquiv n), Fintype.card_sigma]
  congr 1
  ext p
  rw [Fintype.card_prod, Fintype.card_prod, mul_assoc]

end AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS
end

section
/-!
# Ternary trees and the Fuss-Catalan asymptotic

The number of full ternary trees with `n` internal nodes is
`1 / (2n + 1) * binom(3n,n)`.  This file proves the corresponding
Fuss-Catalan asymptotic directly from Stirling's formula.
-/

open Filter Asymptotics
open scoped Topology

lemma ternary_choose_dvd (n : ℕ) :
    2 * n + 1 ∣ Nat.choose (3 * n) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hrel := Nat.choose_succ_right_eq (3 * n) (n - 1)
    have hpred : n - 1 + 1 = n := Nat.sub_one_add_one hn
    have hsub : 3 * n - (n - 1) = 2 * n + 1 := by omega
    rw [hpred, hsub] at hrel
    have hdvd : 2 * n + 1 ∣ Nat.choose (3 * n) n * n := by
      rw [hrel, mul_comm]
      exact dvd_mul_left _ _
    have hcop : Nat.Coprime (2 * n + 1) n := by
      have h : 2 * n + 1 = (n + 1) + n := by omega
      rw [h, Nat.coprime_add_self_left]
      have h2 : n + 1 = 1 + n := by omega
      rw [h2, Nat.coprime_add_self_left]
      simp
    exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hdvd)
end

section
/-!
# The Fuss–Catalan closed form for ternary trees

We prove that the ternary tree count `ternaryCount n` (defined as the cardinality
of the type of full ternary trees with `n` internal nodes, satisfying the
triple-convolution recurrence) equals the Fuss–Catalan number
`binom (3n) n / (2n + 1)`, and connect it to the banked `ternaryTreeCount`.

## Strategy

We work with the *generalized* Fuss–Catalan rationals

`fc s n = s / (3n + s) * binom (3n + s) n`     (s ≥ 1)

and prove the binary-convolution additivity

`∑_{i+j=n} fc s i * fc t j = fc (s+t) n`

by a Gosper-style telescoping argument. Specializing `s = t = 1` then again
folding in one more factor gives the triple convolution `= fc 3 n`, which equals
`fc 1 (n+1)`, i.e. the recurrence for `ternaryCount`.
-/

namespace AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS

open scoped BigOperators
open Finset

/-- Generalized Fuss–Catalan rational:
`fc s n = (s / (3n+s)) * C(3n+s, n)`.  For `s = 1` this is the ordinary ternary
Fuss–Catalan number; the value at `s = 3, n` equals `fc 1 (n+1)`. -/
noncomputable def fc (s n : ℕ) : ℚ :=
  (s : ℚ) / (3 * n + s) * (Nat.choose (3 * n + s) n)

@[simp] lemma fc_zero_right (s : ℕ) (hs : 0 < s) : fc s 0 = 1 := by
  unfold fc
  simp [hs.ne']

/-- Key cross-multiplied binomial identity:
`(2n+1) * C(3n+1, n) = (3n+1) * C(3n, n)`. -/
lemma key_choose_identity (n : ℕ) :
    (2 * n + 1) * Nat.choose (3 * n + 1) n = (3 * n + 1) * Nat.choose (3 * n) n := by
  have h := Nat.choose_mul_succ_eq (3 * n) n
  -- h : C(3n, n) * (3n + 1) = C(3n + 1, n) * (3n + 1 - n)
  have hsub : 3 * n + 1 - n = 2 * n + 1 := by omega
  rw [hsub] at h
  -- h : C(3n,n) * (3n+1) = C(3n+1,n) * (2n+1)
  rw [mul_comm (2 * n + 1), mul_comm (3 * n + 1)]
  exact h.symm

/-- The generalized Fuss–Catalan value at `s = 1` is the banked ternary
Fuss–Catalan number (as a rational): `fc 1 n = C(3n,n)/(2n+1)`. -/
lemma fc_one_eq_ternary (n : ℕ) :
    fc 1 n = (Nat.choose (3 * n) n : ℚ) / (2 * n + 1) := by
  unfold fc
  rw [Nat.cast_one]
  have hd1 : (3 * (n : ℚ) + 1) ≠ 0 := by positivity
  have hd2 : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, one_mul]
  rw [div_eq_div_iff hd1 hd2]
  have hkey := key_choose_identity n
  have : ((2 * n + 1) * Nat.choose (3 * n + 1) n : ℚ)
        = ((3 * n + 1) * Nat.choose (3 * n) n : ℚ) := by exact_mod_cast hkey
  push_cast at this ⊢
  ring_nf
  ring_nf at this
  linarith [this]

/-- Connection to the banked count: `(ternaryTreeCount n : ℚ) = fc 1 n`. -/
lemma ternaryTreeCount_eq_fc_one (n : ℕ) :
    (ternaryTreeCount n : ℚ) = fc 1 n := by
  rw [fc_one_eq_ternary]
  unfold ternaryTreeCount
  rw [Nat.cast_div (ternary_choose_dvd n) (by positivity)]
  push_cast
  ring

end AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS
end

/-!
# Ternary trees via Lagrange inversion

We close the ternary-tree Fuss–Catalan closed form
`ternaryCount n = C(3n, n) / (2n + 1) = ternaryTreeCount n`
through the banked Ch1 Lagrange inversion machinery, mirroring the Catalan
worked example `coeff_implicitSeries_one_add_X_sq` with a cube.

The generating function `B = ∑ ternaryCount n · zⁿ` satisfies `B = 1 + z·B³`, so
`T := B - 1` satisfies `T = z·(1 + T)³ = z·((1+X)³).subst T`. By
`implicitSeries_unique`, `T = implicitSeries ((1+X)³)`, whose `n`-th coefficient
(for `0 < n`) is `(1/n)·C(3n, n-1) = C(3n, n)/(2n+1)` by Lagrange inversion.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS

open PowerSeries
open AnalyticCombinatorics.Ch1.Lagrange
open scoped BigOperators

/-! ## Part B.1 — Lagrange coefficient of `implicitSeries ((1+X)³)` -/

set_option backward.isDefEq.respectTransparency false in
/-- Public coefficient formula for `(1 + X)^m` over `ℚ⟦X⟧`. -/
lemma coeff_one_add_X_pow_rat (m k : ℕ) :
    coeff k ((1 + X : ℚ⟦X⟧) ^ m) = (((m.choose k : ℕ) : ℚ)) := by
  have hright : ((1 + X : ℚ⟦X⟧) ^ m) =
      ((((1 : Polynomial ℚ) + Polynomial.X) ^ m : Polynomial ℚ) : ℚ⟦X⟧) := by
    simp
  rw [hright, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/-- The exact `Nat` binomial identity behind the Fuss–Catalan reduction:
`n · C(3n, n) = (2n+1) · C(3n, n-1)`. -/
lemma nat_choose_three_pred_identity (n : ℕ) (hn : 0 < n) :
    n * Nat.choose (3 * n) n = (2 * n + 1) * Nat.choose (3 * n) (n - 1) := by
  have hchoose := Nat.choose_succ_right_eq (3 * n) (n - 1)
  -- hchoose : C(3n, n-1+1) * (n-1+1) = C(3n, n-1) * (3n - (n-1))
  have hsucc : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hsub : 3 * n - (n - 1) = 2 * n + 1 := by omega
  rw [hsucc, hsub] at hchoose
  -- hchoose : C(3n, n) * n = C(3n, n-1) * (2n+1)
  rw [mul_comm n, mul_comm (2 * n + 1)]
  exact hchoose

/-- Rational form of the Lagrange coefficient as the Fuss–Catalan number. -/
lemma inv_natCast_mul_choose_three_pred_eq_choose_div (n : ℕ) (hn : 0 < n) :
    (n : ℚ)⁻¹ * ((Nat.choose (3 * n) (n - 1) : ℕ) : ℚ)
      = ((Nat.choose (3 * n) n : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ) := by
  have hnat := nat_choose_three_pred_identity n hn
  have hq : (n : ℚ) * ((Nat.choose (3 * n) n : ℕ) : ℚ)
      = ((2 * n + 1 : ℕ) : ℚ) * ((Nat.choose (3 * n) (n - 1) : ℕ) : ℚ) := by
    exact_mod_cast hnat
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hden : ((2 * n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp
  linarith [hq]

/-- The implicit solution of `T = X · (1 + T)³` has Fuss–Catalan coefficients
`C(3n, n)/(2n+1)` for `0 < n`. Cube analogue of `coeff_implicitSeries_one_add_X_sq`. -/
theorem coeff_implicitSeries_one_add_X_cube (n : ℕ) (hn : 0 < n) :
    coeff n (ImplicitSeries.implicitSeries ((1 + X) ^ 3 : ℚ⟦X⟧))
      = ((Nat.choose (3 * n) n : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ) := by
  have hunit : IsUnit (constantCoeff (((1 + X) ^ 3 : ℚ⟦X⟧))) := by
    simp
  have hlag := Residue.lagrange_inversion_divided (R := ℚ)
    (((1 + X) ^ 3 : ℚ⟦X⟧)) hunit n hn
  have hcoeff : coeff (n - 1) ((((1 + X) ^ 3 : ℚ⟦X⟧) ^ n))
      = (((Nat.choose (3 * n) (n - 1) : ℕ) : ℚ)) := by
    have hpow : ((((1 + X) ^ 3 : ℚ⟦X⟧) ^ n) = (1 + X : ℚ⟦X⟧) ^ (3 * n)) := by
      rw [← pow_mul]
    rw [hpow]
    exact coeff_one_add_X_pow_rat (3 * n) (n - 1)
  rw [hcoeff] at hlag
  calc
    coeff n (ImplicitSeries.implicitSeries ((1 + X) ^ 3 : ℚ⟦X⟧))
        = (n : ℚ)⁻¹ * (((Nat.choose (3 * n) (n - 1) : ℕ) : ℚ)) := by
          simpa using hlag
    _ = ((Nat.choose (3 * n) n : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ) :=
          inv_natCast_mul_choose_three_pred_eq_choose_div n hn


/-! ## Part B.2 — connect `ternaryCount` to `implicitSeries ((1+X)³)` -/

/-- The generating function of `ternaryCount` over `ℚ⟦X⟧`. -/
noncomputable def ternaryGF : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => (ternaryCount n : ℚ)

/-- The shifted series `T = B - 1`, with vanishing constant term. -/
noncomputable def ternaryT : ℚ⟦X⟧ :=
  ternaryGF - 1

@[simp] lemma coeff_ternaryGF (n : ℕ) :
    coeff n ternaryGF = (ternaryCount n : ℚ) := by
  simp [ternaryGF]

@[simp] lemma constantCoeff_ternaryGF :
    constantCoeff ternaryGF = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_ternaryGF, ternaryCount_zero]
  norm_num

/-- Reshape the nested antidiagonal double sum (from two `coeff_mul`s) into the
`TripleIndex` sum used by the banked `ternaryCount_succ` recurrence. -/
lemma tripleIndex_sum_eq_nested_antidiag {M : Type*} [AddCommMonoid M] (n : ℕ)
    (g : ℕ → ℕ → ℕ → M) :
    ∑ p : TripleIndex n, g p.val.1 p.val.2.1 p.val.2.2 =
      ∑ x ∈ Finset.antidiagonal n,
        ∑ y ∈ Finset.antidiagonal x.2, g x.1 y.1 y.2 := by
  classical
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun p _ => (⟨(p.val.1, p.val.2.1 + p.val.2.2), (p.val.2.1, p.val.2.2)⟩ :
      (_ : ℕ × ℕ) × ℕ × ℕ))
    (j := fun s hs => (⟨(s.1.1, s.2.1, s.2.2), by
      rw [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_antidiagonal] at hs
      obtain ⟨h1, h2⟩ := hs
      change s.1.1 + s.2.1 + s.2.2 = n
      omega⟩ : TripleIndex n))
    ?hi ?hj ?left ?right ?h
  case hi =>
    rintro ⟨⟨a, b, c⟩, hp⟩ _
    simp only at hp
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_antidiagonal]
    refine ⟨?_, ?_⟩
    · change a + (b + c) = n; omega
    · rfl
  case hj =>
    rintro s hs
    exact Finset.mem_univ _
  case left =>
    rintro ⟨⟨a, b, c⟩, hp⟩ _
    rfl
  case right =>
    rintro ⟨⟨a, d⟩, ⟨b, c⟩⟩ hs
    rw [Finset.mem_sigma, Finset.mem_antidiagonal, Finset.mem_antidiagonal] at hs
    obtain ⟨h1, h2⟩ := hs
    -- goal: i (j s) = s, i.e. ((a, b+c), (b,c)) = ((a,d),(b,c)) ; need b+c = d
    have hd : b + c = d := h2
    subst hd
    rfl
  case h =>
    rintro ⟨⟨a, b, c⟩, hp⟩ _
    rfl

section
end

set_option backward.isDefEq.respectTransparency false in
/-- The triple-convolution coefficient of the cube of the generating function,
matching the banked `ternaryCount_succ` recurrence indexed by `TripleIndex`. -/
lemma coeff_ternaryGF_cube (n : ℕ) :
    coeff n (ternaryGF ^ 3) =
      ∑ p : TripleIndex n,
        (ternaryCount p.val.1 : ℚ) *
        (ternaryCount p.val.2.1 : ℚ) *
        (ternaryCount p.val.2.2 : ℚ) := by
  classical
  have hpow : ternaryGF ^ 3 = ternaryGF * (ternaryGF * ternaryGF) := by ring
  rw [hpow, PowerSeries.coeff_mul]
  rw [tripleIndex_sum_eq_nested_antidiag n
    (fun a b c => (ternaryCount a : ℚ) * (ternaryCount b : ℚ) * (ternaryCount c : ℚ))]
  apply Finset.sum_congr rfl
  intro x _
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp only [coeff_ternaryGF]
  ring

lemma ternaryGF_spec :
    ternaryGF = 1 + X * ternaryGF ^ 3 := by
  ext n
  cases n with
  | zero =>
      simp [coeff_ternaryGF, ternaryCount_zero]
  | succ m =>
      rw [map_add, PowerSeries.coeff_succ_X_mul, coeff_ternaryGF,
        ternaryCount_succ, coeff_ternaryGF_cube]
      push_cast
      simp [mul_assoc]

lemma constantCoeff_ternaryT :
    constantCoeff ternaryT = 0 := by
  rw [ternaryT, map_sub, constantCoeff_ternaryGF]
  simp

section
end

set_option backward.isDefEq.respectTransparency false in
lemma ternaryGF_eq_one_add_ternaryT :
    ternaryGF = 1 + ternaryT := by
  rw [ternaryT]; ring

section
end

set_option backward.isDefEq.respectTransparency false in
lemma ternaryT_spec :
    ternaryT = X * (((1 + X) ^ 3 : ℚ⟦X⟧).subst ternaryT) := by
  have hT0 : constantCoeff ternaryT = 0 := constantCoeff_ternaryT
  have hSubst : PowerSeries.HasSubst ternaryT :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hT0
  have hsubst : ((1 + X) ^ 3 : ℚ⟦X⟧).subst ternaryT = (1 + ternaryT) ^ 3 := by
    rw [PowerSeries.subst_pow hSubst, PowerSeries.subst_add hSubst,
      PowerSeries.subst_X hSubst]
    congr 2
    rw [← PowerSeries.coe_substAlgHom hSubst]
    exact map_one (PowerSeries.substAlgHom hSubst)
  rw [hsubst, ← ternaryGF_eq_one_add_ternaryT]
  -- goal: ternaryT = X * ternaryGF^3
  -- from hB: ternaryGF = 1 + X*ternaryGF^3, and ternaryT = ternaryGF - 1
  rw [ternaryT]
  have hB := ternaryGF_spec
  linear_combination hB

lemma ternaryT_eq_implicit_cube :
    ternaryT = ImplicitSeries.implicitSeries ((1 + X) ^ 3 : ℚ⟦X⟧) :=
  ImplicitSeries.implicitSeries_unique
    ((1 + X) ^ 3 : ℚ⟦X⟧) ternaryT ternaryT_spec constantCoeff_ternaryT

lemma ternaryCount_eq_coeff_implicit_cube (n : ℕ) (hn : 0 < n) :
    (ternaryCount n : ℚ) =
      coeff n (ImplicitSeries.implicitSeries ((1 + X) ^ 3 : ℚ⟦X⟧)) := by
  rw [← ternaryT_eq_implicit_cube, ternaryT, map_sub, coeff_ternaryGF]
  have hone : coeff n (1 : ℚ⟦X⟧) = 0 := by
    rw [PowerSeries.coeff_one]
    simp [Nat.ne_of_gt hn]
  rw [hone, sub_zero]

/-! ## Part B.3 — final Fuss–Catalan closed form + connection to `ternaryTreeCount` -/

/-- Rational closed form: `ternaryCount n = C(3n,n)/(2n+1)`. -/
theorem ternaryCount_eq_fussCatalan_rat (n : ℕ) :
    (ternaryCount n : ℚ) =
      ((Nat.choose (3 * n) n : ℕ) : ℚ) / ((2 * n + 1 : ℕ) : ℚ) := by
  cases n with
  | zero =>
      simp [ternaryCount_zero]
  | succ m =>
      have hn : 0 < m + 1 := Nat.succ_pos m
      rw [ternaryCount_eq_coeff_implicit_cube (m + 1) hn,
        coeff_implicitSeries_one_add_X_cube (m + 1) hn]

end AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch7 AnalyticCombinatorics.Ch7.SingularityApp AnalyticCombinatorics.Ch7.SingularityApp.TernaryTreeNS
open PowerSeries
open AnalyticCombinatorics.Ch1.Lagrange
open scoped BigOperators
theorem solution (n : ℕ) :
    ternaryCount n = _root_.ternaryTreeCount n := by
  have hq : (ternaryCount n : ℚ) = (_root_.ternaryTreeCount n : ℚ) := by
    rw [ternaryCount_eq_fussCatalan_rat, ternaryTreeCount_eq_fc_one, fc_one_eq_ternary]
    norm_num
  exact_mod_cast hq
