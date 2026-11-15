-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.biUnion_cfzCanonicalCarryCell_eq_natBox
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:23:50.224621+00:00
-- url     : https://prove2.me/submissions/228a6a42-959d-43e5-9abe-41725f1d889b

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
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









/-! ## CFZ coefficient and block-diameter facts -/





/-! ## Carry-change hyperplanes -/



















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

section


/-!
# Canonical carry-cell partition independent of divisor choices

The quotient-block argument used so far chooses its block side from the
paired divisor LCM.  Consequently its frozen affine family varies with the
divisor choice, which obstructs a direct comparison with one unrestricted
Euler series.

There is also a divisor-independent decomposition: partition the standard
natural box by the complete vector of canonical CFZ carries.  The carry
range is bounded solely in terms of `k`, so a fixed finite product of
integer intervals contains every realized vector.  Each fiber is a genuine
simultaneous `IsCFZCarryCell`, the fibers are pairwise disjoint, and their
union is the whole box.

This file establishes that exact combinatorial reorganization.  The next
analytic input for this route is a residue-class discrepancy estimate on
these rational polyhedral cells, uniform in the paired divisor modulus.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Carry vectors and their finite range -/





/-- An integer whose natural absolute value is at most `C` lies in the
integer interval `[-C,C]`. -/
theorem mem_Icc_of_natAbs_le
    {c : ℤ} {C : ℕ} (hc : c.natAbs ≤ C) :
    c ∈ Finset.Icc (-(C : ℤ)) (C : ℤ) := by
  rw [Finset.mem_Icc]
  cases c with
  | ofNat n =>
      simp at hc ⊢
      omega
  | negSucc n =>
      simp at hc ⊢
      omega

/-- Every carry vector realized in the standard box belongs to the fixed
finite range. -/
theorem cfzCanonicalCarryVector_mem_choices
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N)) :
    cfzCanonicalCarryVector (N := N) forms x ∈
      cfzCanonicalCarryVectorChoices κ k := by
  apply Fintype.mem_piFinset.mpr
  intro q
  exact
    mem_Icc_of_natAbs_le
      (natAbs_cfzCarry_of_mem_natBox_le (N := N)
        (forms q) hx)

/-! ## The canonical cells -/



@[simp]
theorem mem_cfzCanonicalCarryCell
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (x : CFZVariable k → ℕ) :
    x ∈ cfzCanonicalCarryCell (N := N) forms carry ↔
      x ∈ natBox (fun _ : CFZVariable k => N) ∧
        cfzCanonicalCarryVector (N := N) forms x = carry := by
  simp [cfzCanonicalCarryCell]

/-- A point of the natural box belongs to its own carry-vector fiber. -/
theorem mem_cfzCanonicalCarryCell_self
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N)) :
    x ∈ cfzCanonicalCarryCell (N := N) forms
      (cfzCanonicalCarryVector (N := N) forms x) := by
  exact (mem_cfzCanonicalCarryCell (N := N) forms _ x).mpr
    ⟨hx, rfl⟩





/-! ## Exact partition identities -/







end Wikipedia.SzemeredisTheorem

end
/-!
# Canonical carry-cell partition independent of divisor choices

The quotient-block argument used so far chooses its block side from the
paired divisor LCM.  Consequently its frozen affine family varies with the
divisor choice, which obstructs a direct comparison with one unrestricted
Euler series.

There is also a divisor-independent decomposition: partition the standard
natural box by the complete vector of canonical CFZ carries.  The carry
range is bounded solely in terms of `k`, so a fixed finite product of
integer intervals contains every realized vector.  Each fiber is a genuine
simultaneous `IsCFZCarryCell`, the fibers are pairwise disjoint, and their
union is the whole box.

This file establishes that exact combinatorial reorganization.  The next
analytic input for this route is a residue-class discrepancy estimate on
these rational polyhedral cells, uniform in the paired divisor modulus.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Carry vectors and their finite range -/
/-! ## The canonical cells -/
/-! ## Exact partition identities -/

open Wikipedia.SzemeredisTheorem in
/-- The finite union of all allowed carry fibers is exactly the standard
natural box. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k) :
    (cfzCanonicalCarryVectorChoices κ k).biUnion
        (cfzCanonicalCarryCell (N := N) forms) =
      natBox (fun _ : CFZVariable k => N) := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨carry, _hcarry, hxcell⟩ := hx
    exact
      (mem_cfzCanonicalCarryCell (N := N) forms carry x).mp hxcell |>.1
  · intro hx
    rw [Finset.mem_biUnion]
    exact
      ⟨cfzCanonicalCarryVector (N := N) forms x,
        cfzCanonicalCarryVector_mem_choices (N := N) forms hx,
        mem_cfzCanonicalCarryCell_self (N := N) forms hx⟩
