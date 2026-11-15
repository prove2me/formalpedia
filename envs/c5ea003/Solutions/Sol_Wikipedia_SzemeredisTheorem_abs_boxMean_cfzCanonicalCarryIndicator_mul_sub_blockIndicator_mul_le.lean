-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_boxMean_cfzCanonicalCarryIndicator_mul_sub_blockIndicator_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:46:33.531331+00:00
-- url     : https://prove2.me/submissions/2008fe62-c013-4ea0-a7bc-bceab9cb0320

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_boxMean_sub_boxMean_le_bad

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











end Wikipedia.SzemeredisTheorem

end

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

















@[simp]
theorem mem_cfzCarryBadPoints
    {k N : ℕ} [NeZero N]
    {D : ℕ} {q : CFZFormIndex k}
    {x : CFZVariable k → ℕ} :
    x ∈ cfzCarryBadPoints (N := N) D q ↔
      CFZCarryBadPoint (N := N) D q x := by
  classical
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    exact Finset.mem_filter.mpr ⟨hx.1, hx⟩







/-! ## Explicit bad-point counts -/

















/-! ## Carry-adjusted affine block model -/



/-- A positive-side block base lies in the same quotient block. -/
theorem sameQuotientBlock_quotientBlockBase
    {ι : Type*} {D : ℕ} (hD : 0 < D)
    (x : ι → ℕ) :
    SameQuotientBlock D x (quotientBlockBase D x) := by
  intro i
  rw [quotientBlockBase, Nat.mul_comm,
    Nat.mul_div_left _ hD]

/-- The block base is coordinatewise no larger than the original point. -/
theorem quotientBlockBase_le
    {ι : Type*} (D : ℕ) (x : ι → ℕ) (i : ι) :
    quotientBlockBase D x i ≤ x i := by
  simpa [quotientBlockBase, Nat.mul_comm] using
    Nat.div_mul_le_self (x i) D

/-- Hence the block base of a point in the standard box remains in the
standard box. -/
theorem quotientBlockBase_mem_natBox
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {N D : ℕ} {x : ι → ℕ}
    (hx : x ∈ natBox (fun _ : ι => N)) :
    quotientBlockBase D x ∈ natBox (fun _ : ι => N) := by
  rw [mem_natBox]
  intro i
  exact (quotientBlockBase_le D x i).trans_lt
    (mem_natBox.mp hx i)

















/-- Outside the one-form bad set, the carry at the block base equals the
carry at the point. -/
theorem cfzCarry_quotientBlockBase_eq_of_not_bad
    {k N D : ℕ} [NeZero N] (hD : 0 < D)
    (q : CFZFormIndex k)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hgood : ¬CFZCarryBadPoint (N := N) D q x) :
    cfzCarry (N := N) q (quotientBlockBase D x) =
      cfzCarry (N := N) q x := by
  by_contra hne
  apply hgood
  exact
    ⟨hx, quotientBlockBase D x,
      quotientBlockBase_mem_natBox hx,
      sameQuotientBlock_quotientBlockBase hD x,
      fun h => hne h.symm⟩





/-! ## A normalized disagreement bound -/





















/-! ## Carry-dependent affine residue model -/















end Wikipedia.SzemeredisTheorem

end

section



/-!
# Residue discrepancy on canonical CFZ carry cells

The canonical carry partition freezes the affine family independently of
all divisor choices.  To use it in the divisor expansion, one must still
average a periodic residue function on each carry fiber.

This file starts that comparison at the exact level.  A block indicator
tests the carry vector at the lower corner of a side-`D` quotient block.
On the coordinatewise box trimmed to a multiple of `D`, that indicator
depends only on the quotient coordinate.  It is therefore independent of
every `D`-periodic residue function, and their normalized mean factors
exactly.

The next lemmas compare this block indicator with the genuine canonical
cell indicator.  They can disagree only on the already-counted family
carry-bad set.  Together with the outer trimming boundary this yields the
required `O_{k,m}(D/N)` discrepancy without introducing a new geometric
axiom.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Point and quotient-block indicators -/









/-- Away from the family carry-bad set, sampling the carry vector at the
block base gives the actual carry vector of the point. -/
theorem cfzCanonicalCarryVector_quotientBlockBase_eq_of_not_mem_bad
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D)
    (forms : κ → CFZFormIndex k)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hgood :
      x ∉ cfzFamilyCarryBadPoints (N := N) D forms) :
    cfzCanonicalCarryVector (N := N) forms
        (quotientBlockBase D x) =
      cfzCanonicalCarryVector (N := N) forms x := by
  funext q
  exact cfzCarry_quotientBlockBase_eq_of_not_bad
    hD (forms q) hx (by
      intro hbad
      apply hgood
      apply Finset.mem_biUnion.mpr
      exact
        ⟨q, Finset.mem_univ q,
          mem_cfzCarryBadPoints.mpr hbad⟩)

/-- Consequently the point and block indicators agree away from the family
carry-bad set. -/
theorem cfzCanonicalCarryIndicator_eq_blockIndicator_of_not_mem_bad
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    {x : CFZVariable k → ℕ}
    (hx : x ∈ natBox (fun _ : CFZVariable k => N))
    (hgood :
      x ∉ cfzFamilyCarryBadPoints (N := N) D forms) :
    cfzCanonicalCarryIndicator (N := N) forms carry x =
      cfzCanonicalCarryBlockIndicator
        (N := N) D forms carry x := by
  unfold cfzCanonicalCarryBlockIndicator
    cfzCanonicalCarryIndicator
  rw [cfzCanonicalCarryVector_quotientBlockBase_eq_of_not_mem_bad
    hD forms hx hgood]

/-! ## The carry-bad set inside the complete-block box -/



@[simp]
theorem mem_cfzTrimmedFamilyCarryBadPoints
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    {forms : κ → CFZFormIndex k}
    {x : CFZVariable k → ℕ} :
    x ∈ cfzTrimmedFamilyCarryBadPoints
        (N := N) D forms ↔
      x ∈ cfzFamilyCarryBadPoints (N := N) D forms ∧
        x ∈ natBox
          (fun _ : CFZVariable k => trimToMultiple D N) := by
  simp [cfzTrimmedFamilyCarryBadPoints]

theorem cfzTrimmedFamilyCarryBadPoints_subset_natBox
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D : ℕ) (forms : κ → CFZFormIndex k) :
    cfzTrimmedFamilyCarryBadPoints (N := N) D forms ⊆
      natBox
        (fun _ : CFZVariable k => trimToMultiple D N) := by
  intro x hx
  exact (mem_cfzTrimmedFamilyCarryBadPoints.mp hx).2



/-! ## Exact quotient/residue factorization -/





/-! ## Point/block comparison on the trimmed box -/





/-! ## Canonical-cell residue discrepancy on the trimmed box -/



/-! ## Full-box discrepancy -/



end Wikipedia.SzemeredisTheorem

end
/-!
# Residue discrepancy on canonical CFZ carry cells

The canonical carry partition freezes the affine family independently of
all divisor choices.  To use it in the divisor expansion, one must still
average a periodic residue function on each carry fiber.

This file starts that comparison at the exact level.  A block indicator
tests the carry vector at the lower corner of a side-`D` quotient block.
On the coordinatewise box trimmed to a multiple of `D`, that indicator
depends only on the quotient coordinate.  It is therefore independent of
every `D`-periodic residue function, and their normalized mean factors
exactly.

The next lemmas compare this block indicator with the genuine canonical
cell indicator.  They can disagree only on the already-counted family
carry-bad set.  Together with the outer trimming boundary this yields the
required `O_{k,m}(D/N)` discrepancy without introducing a new geometric
axiom.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Point and quotient-block indicators -/
/-! ## The carry-bad set inside the complete-block box -/
/-! ## Exact quotient/residue factorization -/
/-! ## Point/block comparison on the trimmed box -/

open Wikipedia.SzemeredisTheorem in
/-- Multiplying by a function of absolute value at most one preserves the
point/block disagreement bound. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (F : (CFZVariable k → ℕ) → ℝ)
    (hFbound : ∀ x, |F x| ≤ 1) :
    |boxMean
          (fun _ : CFZVariable k => trimToMultiple D N)
          (fun x =>
            cfzCanonicalCarryIndicator
                (N := N) forms carry x *
              F x) -
        boxMean
          (fun _ : CFZVariable k => trimToMultiple D N)
          (fun x =>
            cfzCanonicalCarryBlockIndicator
                (N := N) D forms carry x *
              F x)| ≤
      ((cfzTrimmedFamilyCarryBadPoints
          (N := N) D forms).card : ℝ) /
        ∏ _v : CFZVariable k,
          (trimToMultiple D N : ℝ) := by
  apply abs_boxMean_sub_boxMean_le_bad
    (fun _ : CFZVariable k => trimToMultiple D N)
    (cfzTrimmedFamilyCarryBadPoints
      (N := N) D forms)
  · exact cfzTrimmedFamilyCarryBadPoints_subset_natBox D forms
  · intro x hx hgood
    have hxN :
        x ∈ natBox (fun _ : CFZVariable k => N) :=
      natBox_trimmed_subset D
        (fun _ : CFZVariable k => N) hx
    have hgoodGlobal :
        x ∉ cfzFamilyCarryBadPoints (N := N) D forms := by
      intro hbad
      apply hgood
      exact mem_cfzTrimmedFamilyCarryBadPoints.mpr
        ⟨hbad, hx⟩
    rw [cfzCanonicalCarryIndicator_eq_blockIndicator_of_not_mem_bad
      hD forms carry hxN hgoodGlobal]
  · intro x _hx
    unfold cfzCanonicalCarryBlockIndicator
      cfzCanonicalCarryIndicator
    by_cases hp :
        cfzCanonicalCarryVector (N := N) forms x = carry
    · by_cases hb :
          cfzCanonicalCarryVector (N := N) forms
              (quotientBlockBase D x) = carry
      · simp [hp, hb]
      · simpa [hp, hb] using hFbound x
    · by_cases hb :
          cfzCanonicalCarryVector (N := N) forms
              (quotientBlockBase D x) = carry
      · simpa [hp, hb, abs_neg] using hFbound x
      · simp [hp, hb]
