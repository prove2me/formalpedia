-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_boxMean_sub_trimmedBoxMean_le_boundary
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:45:11.052197+00:00
-- url     : https://prove2.me/submissions/158b3d64-e636-4b62-b000-3dc7699712f0

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_boxSum_sub_trimmed_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_div_sub_div_le_two_mul_boundary

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
theorem card_natBox {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) :
    (natBox side).card = ∏ i, side i := by
  simp [natBox]



@[simp]
theorem card_finiteBox {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) :
    Fintype.card (FiniteBox side) = ∏ i, side i := by
  simp [FiniteBox]







/-! ## Coordinatewise periodicity and exact box sums -/



























/-! ## Exact means -/









/-! ## Trimming and explicit boundary loss -/





/-- Trimming never increases an interval. -/
theorem trimToMultiple_le (D L : ℕ) :
    trimToMultiple D L ≤ L :=
  Nat.div_mul_le_self L D











theorem trimmedSide_le {ι : Type*}
    (D : ℕ) (side : ι → ℕ) (i : ι) :
    trimmedSide D side i ≤ side i :=
  trimToMultiple_le D (side i)

/-- The coordinatewise trimmed box is contained in the original box. -/
theorem natBox_trimmed_subset {ι : Type*}
    [Fintype ι] [DecidableEq ι] (D : ℕ) (side : ι → ℕ) :
    natBox (trimmedSide D side) ⊆ natBox side := by
  intro x hx
  rw [mem_natBox] at hx ⊢
  intro i
  exact (hx i).trans_le (trimmedSide_le D side i)

/-- Exact boundary cardinality after coordinatewise trimming. -/
theorem card_natBox_sdiff_trimmed {ι : Type*}
    [Fintype ι] [DecidableEq ι] (D : ℕ) (side : ι → ℕ) :
    (natBox side \ natBox (trimmedSide D side)).card =
      (∏ i, side i) - ∏ i, trimToMultiple D (side i) := by
  rw [Finset.card_sdiff_of_subset (natBox_trimmed_subset D side)]
  simp [trimmedSide]





/-- Boundary estimate with the cardinality expanded as an explicit difference
of box volumes. -/
theorem abs_boxSum_sub_trimmed_le_explicit {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (D : ℕ) (side : ι → ℕ) (F : (ι → ℕ) → ℝ) (B : ℝ)
    (hF : ∀ x ∈ natBox side, |F x| ≤ B) :
    |boxSum side F - boxSum (trimmedSide D side) F| ≤
      (((∏ i, side i) -
        ∏ i, trimToMultiple D (side i) : ℕ) : ℝ) * B := by
  simpa [card_natBox_sdiff_trimmed] using
    abs_boxSum_sub_trimmed_le D side F B hF



end Wikipedia.SzemeredisTheorem

end

section




/-!
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





























theorem const_le_mean {α : Type*} [Fintype α] [Nonempty α]
    {f : α → ℝ} {c : ℝ} (hf : ∀ x, c ≤ f x) :
    c ≤ mean f := by
  simpa using mean_mono (f := fun _ => c) (g := f) hf





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
/-!
# Carry-block Euler products for selected CFZ families

The cyclic CFZ lift is not globally periodic modulo a paired divisor LCM:
crossing a representative boundary changes an integer carry.  The preceding
carry-block boundary file replaces that false periodicity by a sound
piecewise-affine model.  This file identifies the exact arithmetic model on
each complete quotient block.

For `D = pairedDivisorLcm z`, a complete block has the form

`x = r + D a`,  with `0 ≤ r_v < D`.

The carry is frozen at the lower corner `D a`.  Thus the block is governed
by the family

`q ↦ cfzCarryAdjustedAffineForm N W b q (cfzCarry q (D a))`.

Its mean over `r` is an exact squarefree CRT Euler product.  Averaging those
products over all complete blocks gives the global blockwise Euler model.
The only losses in comparing it with the original cyclic density are:

* the explicit carry-transition density from `CFZCarryBlockBoundary`;
* the outer partial-block boundary of size
  `O(D * card(CFZVariable k) / N)`.

The affine constants may depend arbitrarily on the block and on the form.
At primes dividing `W` they are still congruent to the reduced residue `b`,
so every supported local density is zero.  At good primes outside `W`,
one-form and rank-two geometry depends only on the coefficients, giving the
usual exact cardinality-at-most-two formula and the uniform `p⁻²` bound.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## A generic natural representative for an affine residue -/
/-! ## Complete quotient blocks and their affine families -/
/-! ## Good complete quotient blocks -/
/-! ## Exact blockwise CRT and averaged Euler products -/
/-! ## The complete-block mean is the averaged Euler product -/
/-! ## The outer partial-block boundary -/

open Wikipedia.SzemeredisTheorem in
/-- Trimming a bounded box function to complete coordinatewise blocks costs
at most twice the relative number of removed points.  This statement needs
no periodicity. -/
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ℕ) (side : ι → ℕ)
    (F : (ι → ℕ) → ℝ) (B : ℝ)
    (hD : 0 < D) (hside : ∀ i, D ≤ side i)
    (hbound : ∀ x, |F x| ≤ B) :
    |boxMean side F - boxMean (trimmedSide D side) F| ≤
      2 *
        (((∏ i, side i) -
          ∏ i, trimToMultiple D (side i) : ℕ) : ℝ) *
        B /
        ∏ i, (side i : ℝ) := by
  have hsidepos : ∀ i, 0 < side i :=
    fun i => hD.trans_le (hside i)
  have htrimpos : ∀ i, 0 < trimmedSide D side i := by
    intro i
    change 0 < side i / D * D
    exact Nat.mul_pos (Nat.div_pos (hside i) hD) hD
  have hprodle :
      (∏ i, trimmedSide D side i) ≤ ∏ i, side i := by
    apply Finset.prod_le_prod
    · intro i _hi
      exact Nat.zero_le _
    · intro i _hi
      exact trimmedSide_le D side i
  have hvolume :
      (∏ i, (side i : ℝ)) -
          ∏ i, (trimmedSide D side i : ℝ) =
        (((∏ i, side i) -
          ∏ i, trimmedSide D side i : ℕ) : ℝ) := by
    rw [← Nat.cast_prod, ← Nat.cast_prod, Nat.cast_sub hprodle]
  have hsum :
      |boxSum side F - boxSum (trimmedSide D side) F| ≤
        (((∏ i, side i) -
          ∏ i, trimmedSide D side i : ℕ) : ℝ) * B :=
    abs_boxSum_sub_trimmed_le_explicit D side F B
      (fun x _hx => hbound x)
  have hV : 0 < ∏ i, (side i : ℝ) := by
    apply Finset.prod_pos
    intro i _hi
    exact_mod_cast hsidepos i
  have hU : 0 < ∏ i, (trimmedSide D side i : ℝ) := by
    apply Finset.prod_pos
    intro i _hi
    exact_mod_cast htrimpos i
  have hE :
      0 ≤ (((∏ i, side i) -
        ∏ i, trimmedSide D side i : ℕ) : ℝ) := by
    positivity
  have htrimmean :
      |boxSum (trimmedSide D side) F /
          ∏ i, (trimmedSide D side i : ℝ)| ≤ B := by
    rw [← boxMean]
    rw [boxMean_eq_mean_finiteBox]
    let x₀ : FiniteBox (trimmedSide D side) :=
      fun i => ⟨0, htrimpos i⟩
    let : Nonempty (FiniteBox (trimmedSide D side)) := ⟨x₀⟩
    apply abs_le.mpr
    constructor
    · exact
        const_le_mean
          (fun x =>
            neg_le_of_abs_le
              (hbound (fun i => (x i : ℕ))))
    · exact
        mean_le_of_le_const
          (fun x =>
            le_of_abs_le
              (hbound (fun i => (x i : ℕ))))
  have hnormalize :=
    abs_div_sub_div_le_two_mul_boundary
      hV hU hE hvolume hsum htrimmean
  change
    |boxMean side F - boxMean (trimmedSide D side) F| ≤
      2 *
        (((∏ i, side i) -
          ∏ i, trimmedSide D side i : ℕ) : ℝ) *
        B /
        ∏ i, (side i : ℝ) at hnormalize
  simpa [trimmedSide] using hnormalize
