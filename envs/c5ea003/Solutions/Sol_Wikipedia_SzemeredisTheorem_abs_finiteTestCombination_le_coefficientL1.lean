-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_finiteTestCombination_le_coefficientL1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:05:01.618139+00:00
-- url     : https://prove2.me/submissions/3735b2ac-7578-4f68-9f82-2921b473a7ce

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped Pointwise























theorem IsUnitBounded.nonneg
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, 0 ≤ g x :=
  hg.1

theorem IsUnitBounded.le_one
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, g x ≤ 1 :=
  hg.2





























































































































end Wikipedia.SzemeredisTheorem

end

section



/-!
# Polynomial approximation in the finite dense-model argument

This file formalizes the polynomial part of the dense-model theorem.  A
normalized linear combination of `[0,1]`-valued tests takes values in
`[-1,1]`.  Weierstrass therefore approximates its positive part by a fixed
real polynomial.  Expanding that polynomial reduces correlation with the
majorant to correlations with finite products of the original tests.

The resulting estimates are quantitative and finite.  In particular, the
degree and coefficient loss of the approximating polynomial remain visible;
no asymptotic assertion about a particular pseudorandom majorant is hidden here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite products and polynomial expansions -/









@[simp]
theorem finiteTestCombination_apply
    {Ω τ : Type*} [Fintype τ]
    (q : τ → Ω → ℝ) (c : τ → ℝ) (x : Ω) :
    finiteTestCombination q c x = ∑ t, c t * q t x := by
  classical
  simp [finiteTestCombination]

















/-! ## Bounded combinations and approximation of positive part -/













/-! ## Quantitative positive-part correlation -/













end Wikipedia.SzemeredisTheorem

end
/-!
# Polynomial approximation in the finite dense-model argument

This file formalizes the polynomial part of the dense-model theorem.  A
normalized linear combination of `[0,1]`-valued tests takes values in
`[-1,1]`.  Weierstrass therefore approximates its positive part by a fixed
real polynomial.  Expanding that polynomial reduces correlation with the
majorant to correlations with finite products of the original tests.

The resulting estimates are quantitative and finite.  In particular, the
degree and coefficient loss of the approximating polynomial remain visible;
no asymptotic assertion about a particular pseudorandom majorant is hidden here.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial
/-! ## Finite products and polynomial expansions -/
/-! ## Bounded combinations and approximation of positive part -/

open Wikipedia.SzemeredisTheorem in
/-- A test combination is pointwise bounded by the coefficient `ℓ¹`-norm
when every test is `[0,1]`-valued. -/
theorem solution
    {Ω τ : Type*} [Fintype τ]
    {q : τ → Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    (c : τ → ℝ) (x : Ω) :
    |finiteTestCombination q c x| ≤ coefficientL1 c := by
  classical
  rw [finiteTestCombination_apply]
  calc
    |∑ t, c t * q t x| ≤ ∑ t, |c t * q t x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t, |c t| := by
      apply Finset.sum_le_sum
      intro t ht
      rw [abs_mul]
      have habs : |q t x| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [(hq t).nonneg x]
        · exact (hq t).le_one x
      exact mul_le_of_le_one_right (abs_nonneg (c t)) habs
    _ = coefficientL1 c := by
      rfl
