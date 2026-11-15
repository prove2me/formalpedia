-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_boxMean_sub_boxMean_le_bad
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:45:11.10321+00:00
-- url     : https://prove2.me/submissions/3227481f-7958-47d5-88bb-d2ad4892dffc

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_mean_sub_mean_le_bad

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section







/-!
# Congruence averages on finite boxes

This file supplies the elementary finite-arithmetic layer used after expanding
the Selberg sieve weight.  A finite family of divisor moduli is combined by an
LCM, while a function depending only on coordinatewise residues is averaged
exactly over boxes whose side lengths are multiples of that LCM.

There are two equivalent box models:

* `natBox side` is the literal finset of natural-valued points satisfying
  `x i < side i`;
* `FiniteBox side` is the finite type `∀ i, Fin (side i)`.

The second model makes quotient--remainder reindexing transparent, and
`boxSum_eq_sum_natBox` transports its sums back to the literal finset.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## LCM bounds -/









/-! ## Finite boxes -/









@[simp]
theorem card_finiteBox {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) :
    Fintype.card (FiniteBox side) = ∏ i, side i := by
  simp [FiniteBox]







/-! ## Coordinatewise periodicity and exact box sums -/



























/-! ## Exact means -/









/-! ## Trimming and explicit boundary loss -/































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









/-! ## Canonical carry cells -/

















/-! ## Divisibility indicators modulo a common multiple -/







/-! ## Exact finite-box and residue-vector reindexing -/

/-- `boxMean` is the ordinary normalized mean on its typed finite box. -/
theorem boxMean_eq_mean_finiteBox
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) (F : (ι → ℕ) → ℝ) :
    boxMean side F =
      mean (fun x : FiniteBox side => F (fun i => x i)) := by
  rw [boxMean, boxSum, mean, Fintype.expect_eq_sum_div_card,
    card_finiteBox]
  simp only [Nat.cast_prod]









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































/-! ## A normalized disagreement bound -/



@[simp]
theorem mem_finiteBoxBadSet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {side : ι → ℕ} {bad : Finset (ι → ℕ)}
    {x : FiniteBox side} :
    x ∈ finiteBoxBadSet side bad ↔
      (fun i => (x i : ℕ)) ∈ bad := by
  classical
  simp [finiteBoxBadSet]

/-- If the natural bad set lies in the box, its typed pullback has no larger
cardinality. -/
theorem card_finiteBoxBadSet_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) (bad : Finset (ι → ℕ))
    (_hbad : bad ⊆ natBox side) :
    (finiteBoxBadSet side bad).card ≤ bad.card := by
  classical
  let coePoint : FiniteBox side → (ι → ℕ) :=
    fun x i => (x i : ℕ)
  apply Finset.card_le_card_of_injOn coePoint
  · intro x hx
    exact mem_finiteBoxBadSet.mp hx
  · intro x _hx y _hy hxy
    funext i
    exact Fin.ext (congrFun hxy i)















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
/-! ## Explicit bad-point counts -/
/-! ## Carry-adjusted affine block model -/
/-! ## A normalized disagreement bound -/

open Wikipedia.SzemeredisTheorem in
/-- Natural-box form of the normalized disagreement estimate. -/
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) (bad : Finset (ι → ℕ))
    (F G : (ι → ℕ) → ℝ)
    (hbad : bad ⊆ natBox side)
    (heq : ∀ x ∈ natBox side, x ∉ bad → F x = G x)
    (hbound : ∀ x ∈ natBox side, |F x - G x| ≤ 1) :
    |boxMean side F - boxMean side G| ≤
      (bad.card : ℝ) / ∏ i, (side i : ℝ) := by
  rw [boxMean_eq_mean_finiteBox,
    boxMean_eq_mean_finiteBox]
  let typedBad := finiteBoxBadSet side bad
  have htyped :=
    abs_mean_sub_mean_le_bad typedBad
      (fun x : FiniteBox side => F (fun i => (x i : ℕ)))
      (fun x : FiniteBox side => G (fun i => (x i : ℕ)))
      (fun x hx => by
        apply heq (fun i => (x i : ℕ))
        · rw [mem_natBox]
          exact fun i => (x i).isLt
        · simpa only [typedBad, mem_finiteBoxBadSet] using hx)
      (fun x =>
        hbound (fun i => (x i : ℕ))
          (by
            rw [mem_natBox]
            exact fun i => (x i).isLt))
  have hcard :
      (typedBad.card : ℝ) ≤ (bad.card : ℝ) := by
    exact_mod_cast card_finiteBoxBadSet_le side bad hbad
  rw [card_finiteBox] at htyped
  have hdiv :
      (typedBad.card : ℝ) /
          ((∏ i, side i : ℕ) : ℝ) ≤
        (bad.card : ℝ) /
          ((∏ i, side i : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hcard
      (show
        (0 : ℝ) ≤ ((∏ i, side i : ℕ) : ℝ) by
          positivity)
  exact htyped.trans (by
    simpa only [Nat.cast_prod] using hdiv)
