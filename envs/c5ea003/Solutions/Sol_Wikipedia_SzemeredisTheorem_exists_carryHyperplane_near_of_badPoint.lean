-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_carryHyperplane_near_of_badPoint
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:23:50.322338+00:00
-- url     : https://prove2.me/submissions/a1d18a98-81b7-4386-9de6-12d4c8371e8f

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_carryHyperplane_between_cfzAffineForm_evals
import Theorems.Thm_Wikipedia_SzemeredisTheorem_natAbs_cfzAffineForm_eval_sub_eval_le_of_sameQuotientBlock
import Theorems.Thm_Wikipedia_SzemeredisTheorem_natAbs_cfzCarry_finiteBox_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Geometry of integer affine-form systems

The Goldston--Yıldırım estimate is stated for finite systems of integer
affine forms with nonzero, pairwise non-proportional coefficient vectors and
uniformly bounded coefficients.  This file packages those hypotheses and
verifies them for the Conlon--Fox--Zhao progression forms.
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm





end AffineForm











@[simp]
theorem cfzAffineForm_constant {k : ℕ} (q : CFZFormIndex k) :
    (cfzAffineForm q).constant = 0 :=
  rfl

@[simp]
theorem cfzAffineForm_coefficient {k : ℕ}
    (q : CFZFormIndex k) :
    (cfzAffineForm q).coefficient = cfzCoefficient q :=
  rfl









end Wikipedia.SzemeredisTheorem

end

section



/-!
# Carry-block boundaries for the cyclic CFZ lift

The standard representative of a CFZ form modulo `N` is not periodic in the
natural input coordinates.  This file gives the unconditional replacement
for the false periodicity step.

We divide the standard box into coordinatewise quotient blocks of side `D`.
On a block where every selected CFZ carry is constant, the cyclic lift is an
ordinary affine form with a carry-dependent constant.  A block on which one
carry changes must cross a hyperplane at an integral multiple of `N`.
Because CFZ coefficients are bounded and every CFZ form has a coefficient
equal to `1` or `-1`, the union of all such blocks has an explicit
codimension-one cardinality bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Coordinate quotient blocks -/



















/-! ## A generic unit-coefficient strip count -/



@[simp]
theorem mem_affineStripInBox {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {N L : ℕ} {ψ : AffineForm ι ℤ} {a : ℤ}
    {x : ι → ℕ} :
    x ∈ affineStripInBox N L ψ a ↔
      x ∈ natBox (fun _ : ι => N) ∧
        Int.natAbs
          (ψ.eval (fun i => (x i : ℤ)) - a) ≤ L := by
  simp [affineStripInBox]





/-! ## CFZ coefficient and block-diameter facts -/





/-! ## Carry-change hyperplanes -/









/-- In a linearly ordered triple, the left subinterval has no larger
integer length than the whole interval. -/
theorem natAbs_sub_le_natAbs_sub_of_le_of_le
    {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    Int.natAbs (a - b) ≤ Int.natAbs (a - c) := by
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs,
    Int.natCast_natAbs,
    abs_of_nonpos (sub_nonpos.mpr hab),
    abs_of_nonpos (sub_nonpos.mpr (hab.trans hbc))]
  omega

/-- The analogous bound for the right subinterval. -/
theorem natAbs_sub_le_natAbs_sub_of_le_of_le_right
    {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    Int.natAbs (c - b) ≤ Int.natAbs (c - a) := by
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs,
    Int.natCast_natAbs,
    abs_of_nonneg (sub_nonneg.mpr hbc),
    abs_of_nonneg (sub_nonneg.mpr (hab.trans hbc))]
  omega







/-- Natural-box version of the uniform carry bound. -/
theorem natAbs_cfzCarry_of_mem_natBox_le
    {k N : ℕ} [NeZero N]
    (q : CFZFormIndex k)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N)) :
    Int.natAbs (cfzCarry (N := N) q x) ≤
      cfzCarryRange k := by
  let x' : FiniteBox (fun _ : CFZVariable k => N) :=
    fun v => ⟨x v, mem_natBox.mp hx v⟩
  have hbound :=
    natAbs_cfzCarry_finiteBox_le (N := N) q x'
  simpa [cfzCarryRange, x'] using hbound





/-! ## Explicit bad-point counts -/

















/-! ## Carry-adjusted affine block model -/































/-! ## A normalized disagreement bound -/





















/-! ## Carry-dependent affine residue model -/















end Wikipedia.SzemeredisTheorem

end
/-!
# Carry-block boundaries for the cyclic CFZ lift

The standard representative of a CFZ form modulo `N` is not periodic in the
natural input coordinates.  This file gives the unconditional replacement
for the false periodicity step.

We divide the standard box into coordinatewise quotient blocks of side `D`.
On a block where every selected CFZ carry is constant, the cyclic lift is an
ordinary affine form with a carry-dependent constant.  A block on which one
carry changes must cross a hyperplane at an integral multiple of `N`.
Because CFZ coefficients are bounded and every CFZ form has a coefficient
equal to `1` or `-1`, the union of all such blocks has an explicit
codimension-one cardinality bound.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Coordinate quotient blocks -/
/-! ## A generic unit-coefficient strip count -/
/-! ## CFZ coefficient and block-diameter facts -/
/-! ## Carry-change hyperplanes -/

open Wikipedia.SzemeredisTheorem in
/-- Every bad point lies in a width-`cfzBlockVariation k D` strip around a
carry hyperplane whose index is in the uniform carry range. -/
theorem solution
    {k N D : ℕ} [NeZero N] (hD : 0 < D)
    (q : CFZFormIndex k) (x : CFZVariable k → ℕ)
    (hx : CFZCarryBadPoint (N := N) D q x) :
    ∃ c : ℤ,
      Int.natAbs c ≤ cfzCarryRange k ∧
        x ∈ affineStripInBox N (cfzBlockVariation k D)
          (cfzAffineForm q) ((N : ℤ) * c) := by
  obtain ⟨hxbox, y, hybox, hxy, hcarry⟩ := hx
  obtain ⟨c, hc, hbetween⟩ :=
    exists_carryHyperplane_between_cfzAffineForm_evals
      (N := N) q x y hcarry
  have hdiam :
      Int.natAbs
          ((cfzAffineForm q).eval (fun v => (x v : ℤ)) -
            (cfzAffineForm q).eval (fun v => (y v : ℤ))) ≤
        cfzBlockVariation k D := by
    exact
      natAbs_cfzAffineForm_eval_sub_eval_le_of_sameQuotientBlock
        hD q hxy
  have hcbound :
      Int.natAbs c ≤ cfzCarryRange k := by
    rcases hc with rfl | rfl
    · exact natAbs_cfzCarry_of_mem_natBox_le q hxbox
    · exact natAbs_cfzCarry_of_mem_natBox_le q hybox
  refine ⟨c, hcbound, mem_affineStripInBox.mpr ⟨hxbox, ?_⟩⟩
  rcases hbetween with hbetween | hbetween
  · exact
      (natAbs_sub_le_natAbs_sub_of_le_of_le
        hbetween.1.le hbetween.2).trans hdiam
  · exact
      (natAbs_sub_le_natAbs_sub_of_le_of_le_right
        hbetween.1.le hbetween.2).trans hdiam
