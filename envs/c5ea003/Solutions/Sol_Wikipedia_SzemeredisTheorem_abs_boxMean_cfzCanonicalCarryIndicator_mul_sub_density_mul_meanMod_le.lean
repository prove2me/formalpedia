-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_boxMean_cfzCanonicalCarryIndicator_mul_sub_density_mul_meanMod_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:51:47.702067+00:00
-- url     : https://prove2.me/submissions/c1fd3b5b-391e-4c6e-aa2f-89726b862fce

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_boxMean_cfzCanonicalCarryIndicator_mul_sub_blockIndicator_mul_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_boxMean_cfzCanonicalCarryBlockIndicator_mul_periodic_eq_mul

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







/-- The exact residue-box mean can be reindexed by standard `ZMod`
representatives. -/
theorem meanMod_eq_mean_zmodVector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ℕ) [NeZero D] (F : (ι → ℕ) → ℝ) :
    meanMod D F =
      mean (fun x : ι → ZMod D => F (fun i => (x i).val)) := by
  rw [meanMod, boxMean_eq_mean_finiteBox]
  unfold mean
  apply Fintype.expect_equiv (finiteBoxEquivZModVector D)
  intro x
  congr 1
  funext i
  exact (ZMod.val_natCast_of_lt (x i).isLt).symm

/-! ## Reindexing the cyclic CFZ cube -/







/-! ## CFZ periodicity under lift compatibility -/







/-! ## The exact affine residue model -/













/-! ## Normalized trimming loss -/



/-- A globally bounded function has a bounded exact residue-class mean. -/
theorem abs_meanMod_le_of_abs_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ℕ} (hD : 0 < D)
    (F : (ι → ℕ) → ℝ) (B : ℝ)
    (hF : ∀ x, |F x| ≤ B) :
    |meanMod D F| ≤ B := by
  let : NeZero D := ⟨hD.ne'⟩
  rw [meanMod_eq_mean_zmodVector]
  apply abs_le.mpr
  constructor
  · exact const_le_mean fun x => neg_le_of_abs_le (hF fun i => (x i).val)
  · exact mean_le_of_le_const fun x => le_of_abs_le (hF fun i => (x i).val)



/-! ## Paired divisibility specialization -/









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













/-! ## The carry-bad set inside the complete-block box -/









/-! ## Exact quotient/residue factorization -/





/-! ## Point/block comparison on the trimmed box -/



/-- The same comparison for the unweighted cell indicators. -/
theorem abs_boxMean_cfzCanonicalCarryIndicator_sub_blockIndicator_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) :
    |boxMean
          (fun _ : CFZVariable k => trimToMultiple D N)
          (cfzCanonicalCarryIndicator
            (N := N) forms carry) -
        boxMean
          (fun _ : CFZVariable k => trimToMultiple D N)
          (cfzCanonicalCarryBlockIndicator
            (N := N) D forms carry)| ≤
      ((cfzTrimmedFamilyCarryBadPoints
          (N := N) D forms).card : ℝ) /
        ∏ _v : CFZVariable k,
          (trimToMultiple D N : ℝ) := by
  simpa only [mul_one] using
    abs_boxMean_cfzCanonicalCarryIndicator_mul_sub_blockIndicator_mul_le
      hD forms carry
      (fun _ : CFZVariable k → ℕ => (1 : ℝ))
      (fun _ => by norm_num)

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
/-! ## Canonical-cell residue discrepancy on the trimmed box -/

open Wikipedia.SzemeredisTheorem in
/-- On the complete-block box, the mean of a periodic function restricted
to one canonical carry fiber differs from the fiber density times the
residue mean only through carry-bad blocks. -/
theorem
    solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hD : 0 < D) (hDN : D ≤ N)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (F : (CFZVariable k → ℕ) → ℝ)
    (hperiodic : PeriodicInEachCoordinate F D)
    (hFbound : ∀ x, |F x| ≤ 1) :
    |boxMean
          (fun _ : CFZVariable k => trimToMultiple D N)
          (fun x =>
            cfzCanonicalCarryIndicator
                (N := N) forms carry x *
              F x) -
        boxMean
            (fun _ : CFZVariable k => trimToMultiple D N)
            (cfzCanonicalCarryIndicator
              (N := N) forms carry) *
          meanMod D F| ≤
      2 *
        (((cfzTrimmedFamilyCarryBadPoints
            (N := N) D forms).card : ℝ) /
          ∏ _v : CFZVariable k,
            (trimToMultiple D N : ℝ)) := by
  let side : CFZVariable k → ℕ :=
    fun _ => trimToMultiple D N
  let pointI : (CFZVariable k → ℕ) → ℝ :=
    cfzCanonicalCarryIndicator (N := N) forms carry
  let blockI : (CFZVariable k → ℕ) → ℝ :=
    cfzCanonicalCarryBlockIndicator
      (N := N) D forms carry
  let δ : ℝ :=
    ((cfzTrimmedFamilyCarryBadPoints
        (N := N) D forms).card : ℝ) /
      ∏ _v : CFZVariable k,
        (trimToMultiple D N : ℝ)
  let A : ℝ := boxMean side (fun x => pointI x * F x)
  let B : ℝ := boxMean side (fun x => blockI x * F x)
  let C : ℝ := boxMean side pointI
  let Q : ℝ := boxMean side blockI
  let μ : ℝ := meanMod D F
  have hAB : |A - B| ≤ δ := by
    simpa only [A, B, side, pointI, blockI, δ] using
      abs_boxMean_cfzCanonicalCarryIndicator_mul_sub_blockIndicator_mul_le
        hD forms carry F hFbound
  have hCQ : |C - Q| ≤ δ := by
    simpa only [C, Q, side, pointI, blockI, δ] using
      abs_boxMean_cfzCanonicalCarryIndicator_sub_blockIndicator_le
        hD forms carry
  have hQμ : B = Q * μ := by
    simpa only [B, Q, side, blockI, μ] using
      boxMean_cfzCanonicalCarryBlockIndicator_mul_periodic_eq_mul
        hD hDN forms carry F hperiodic
  have hμ : |μ| ≤ 1 := by
    simpa only [μ] using
      abs_meanMod_le_of_abs_le hD F 1 hFbound
  have hδ : 0 ≤ δ := by
    dsimp only [δ]
    positivity
  have hdecomp :
      A - C * μ = (A - B) + (Q - C) * μ := by
    rw [hQμ]
    ring
  change |A - C * μ| ≤ 2 * δ
  rw [hdecomp]
  calc
    |(A - B) + (Q - C) * μ| ≤
        |A - B| + |(Q - C) * μ| :=
      abs_add_le _ _
    _ = |A - B| + |Q - C| * |μ| := by
      rw [abs_mul]
    _ ≤ δ + δ * 1 := by
      gcongr
      simpa only [abs_sub_comm] using hCQ
    _ = 2 * δ := by ring
