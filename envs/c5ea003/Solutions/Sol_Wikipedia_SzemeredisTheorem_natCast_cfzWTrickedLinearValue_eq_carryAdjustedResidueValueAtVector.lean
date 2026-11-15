-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.natCast_cfzWTrickedLinearValue_eq_carryAdjustedResidueValueAtVector
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:57:46.718875+00:00
-- url     : https://prove2.me/submissions/8f3d8c56-b40b-4fbf-85b9-59e83237e696

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
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
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
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
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cfzAffineForm_eval_eq_val_add_mul_cfzCarry
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cfzCarryAdjustedAffineForm_eval

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
# Small-prime local factors for W-tricked affine forms

If `ψ` is an integer affine form, the affine form occurring after the
`W`-trick is

`x ↦ W * ψ(x) + b`.

At a prime `p ∣ W` this form is identically `b` modulo `p`.  When `b` is a
reduced residue modulo `W`, it is therefore nowhere zero modulo `p`.  This
makes every small-prime avoidance factor, including the complex factor
produced by paired Fourier inversion, exactly one.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem wTrickedAffineForm_constant {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) :
    (wTrickedAffineForm W b ψ).constant =
      (W : ℤ) * ψ.constant + b :=
  rfl

@[simp]
theorem wTrickedAffineForm_coefficient {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) (i : ι) :
    (wTrickedAffineForm W b ψ).coefficient i =
      (W : ℤ) * ψ.coefficient i :=
  rfl



























end Wikipedia.SzemeredisTheorem

end

section



/-!
# Finite-box congruence boundaries for the CFZ divisor expansion

This file isolates the exact finite-box step between the divisor expansion
and the prime-local arithmetic.  It has three layers.

* A normalized boundary estimate compares a bounded periodic function on a
  natural box with its exact residue-class mean.
* Coordinatewise `Fin`/`ZMod` equivalences identify the mean on a
  `CubePoint k N` with the corresponding natural box mean.
* For the cyclic representative used by `cfzWTrickedLinearValue`, periodicity
  modulo a divisor modulus `D` is proved under the precise compatibility
  hypothesis `D ∣ W * N`.

The compatibility hypothesis in the last item is mathematically necessary
for this direct rectangular trimming argument: reducing a form modulo `N`
can change an integer lift by a multiple of `N`, and the subsequent
`W`-trick changes its value by a multiple of `W * N`.  Without divisibility
by `D`, an unconditional treatment must subdivide the box into carry cells
on which every modular reduction has a fixed integer lift.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Why cyclic representatives need a compatibility or carry argument -/





/-! ## Weighted lifts through two moduli -/



/-! ## Natural representatives of CFZ cube points -/





/-- Casting an integer affine evaluation agrees with first reducing all
inputs and coefficients modulo the target modulus. -/
theorem AffineForm.intCast_eval_eq_evalZMod
    {ι : Type*} [Fintype ι]
    (D : ℕ) (ψ : AffineForm ι ℤ) (x : ι → ℤ) :
    ((ψ.eval x : ℤ) : ZMod D) =
      ψ.evalZMod D (fun i => (x i : ZMod D)) := by
  simp only [AffineForm.eval, AffineForm.evalZMod,
    AffineForm.linearMapZMod]
  push_cast
  rfl



/-! ## Canonical carry cells -/

















/-! ## Divisibility indicators modulo a common multiple -/







/-! ## Exact finite-box and residue-vector reindexing -/











/-! ## Reindexing the cyclic CFZ cube -/







/-! ## CFZ periodicity under lift compatibility -/







/-! ## The exact affine residue model -/













/-! ## Normalized trimming loss -/







/-! ## Paired divisibility specialization -/









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

























/-! ## Explicit bad-point counts -/

















/-! ## Carry-adjusted affine block model -/

















/-- With the canonical carry, the adjusted affine evaluation is literally
the natural cyclic lift viewed as an integer. -/
theorem cfzCarryAdjustedAffineForm_eval_canonicalCarry
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (q : CFZFormIndex k)
    (x : CFZVariable k → ℕ) :
    (cfzCarryAdjustedAffineForm N W b q
        (cfzCarry (N := N) q x)).eval
        (fun v => (x v : ℤ)) =
      (cfzWTrickedLinearValue W b q
        (cubePointOfNat (N := N) x) : ℤ) := by
  rw [cfzCarryAdjustedAffineForm_eval,
    cfzAffineForm_eval_eq_val_add_mul_cfzCarry
      (N := N)]
  unfold cfzWTrickedLinearValue wTrickedValue
  push_cast
  ring













/-! ## A normalized disagreement bound -/





















/-! ## Carry-dependent affine residue model -/















end Wikipedia.SzemeredisTheorem

end

section



/-!
# Fixed-family Euler products on canonical CFZ carry cells

The canonical carry vector is chosen before the paired divisor variables.
On one of its fibers, every cyclic CFZ value is represented by one fixed
carry-adjusted affine family.  This file defines its residue model, proves
periodicity and the exact CRT Euler product, and inserts it into the
canonical-cell discrepancy theorem.

Unlike the quotient-block Euler average, the affine family in this file
does not depend on the divisor LCM.  This is the structural feature needed
to compare the coordinatewise-truncated divisor expansion with one
unrestricted prime-support Euler series.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A fixed family attached to one canonical carry vector -/





@[simp]
theorem natCast_cfzCarryAdjustedResidueValueAtVector
    {κ : Type*} {k D : ℕ} [NeZero D]
    (N W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (q : κ)
    (x : CFZVariable k → ZMod D) :
    (cfzCarryAdjustedResidueValueAtVector
        (D := D) N W b forms carry q x : ZMod D) =
      (cfzCarryAdjustedFamilyAtVector
        N W b forms carry q).evalZMod D x := by
  exact ZMod.natCast_zmod_val _

/-! ## Periodicity -/





/-! ## Agreement with the cyclic value on one canonical cell -/







/-! ## Exact residue mean and CRT product -/





/-! ## Per-cell cyclic-to-Euler comparison -/



























/-! ## Summing the canonical carry cells -/









end Wikipedia.SzemeredisTheorem

end
/-!
# Fixed-family Euler products on canonical CFZ carry cells

The canonical carry vector is chosen before the paired divisor variables.
On one of its fibers, every cyclic CFZ value is represented by one fixed
carry-adjusted affine family.  This file defines its residue model, proves
periodicity and the exact CRT Euler product, and inserts it into the
canonical-cell discrepancy theorem.

Unlike the quotient-block Euler average, the affine family in this file
does not depend on the divisor LCM.  This is the structural feature needed
to compare the coordinatewise-truncated divisor expansion with one
unrestricted prime-support Euler series.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## A fixed family attached to one canonical carry vector -/
/-! ## Periodicity -/
/-! ## Agreement with the cyclic value on one canonical cell -/

open Wikipedia.SzemeredisTheorem in
/-- If the point has the prescribed carry vector, the cyclic CFZ value and
the fixed affine residue value agree modulo every positive modulus. -/
theorem
    solution
    {κ : Type*}
    {k N D : ℕ} [NeZero N] [NeZero D]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (q : κ)
    (x : CFZVariable k → ℕ)
    (hcarry :
      cfzCanonicalCarryVector (N := N) forms x = carry) :
    (cfzWTrickedLinearValue W b (forms q)
        (cubePointOfNat (N := N) x) : ZMod D) =
      (cfzCarryAdjustedResidueValueAtVector
        (D := D) N W b forms carry q
        (fun v => (x v : ZMod D)) : ZMod D) := by
  classical
  rw [natCast_cfzCarryAdjustedResidueValueAtVector]
  calc
    (cfzWTrickedLinearValue W b (forms q)
        (cubePointOfNat (N := N) x) : ZMod D) =
        (((cfzCarryAdjustedAffineForm N W b (forms q)
          (cfzCarry (N := N) (forms q) x)).eval
          (fun v => (x v : ℤ)) : ℤ) : ZMod D) := by
      simpa only [Int.cast_natCast] using
        congrArg (fun n : ℤ => (n : ZMod D))
          (cfzCarryAdjustedAffineForm_eval_canonicalCarry
            (N := N) W b (forms q) x).symm
    _ = (((cfzCarryAdjustedAffineForm N W b (forms q)
          (carry q)).eval
          (fun v => (x v : ℤ)) : ℤ) : ZMod D) := by
      have hqcarry := congrFun hcarry q
      change
        cfzCarry (N := N) (forms q) x = carry q
        at hqcarry
      rw [hqcarry]
    _ = (cfzCarryAdjustedFamilyAtVector
          N W b forms carry q).evalZMod D
          (fun v => (x v : ZMod D)) := by
      simpa only [cfzCarryAdjustedFamilyAtVector,
        Int.cast_natCast] using
        AffineForm.intCast_eval_eq_evalZMod D
          (cfzCarryAdjustedFamilyAtVector
            N W b forms carry q)
          (fun v => (x v : ℤ))
