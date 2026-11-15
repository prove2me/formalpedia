-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.sum_cfzCanonicalCarryCellDensity_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:45:56.026663+00:00
-- url     : https://prove2.me/submissions/cef2ed5f-37ff-4541-9b84-04593502734a

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorRankinTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailPolylog
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PrimeHarmonicProductBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_UnrestrictedPrimeSupportEulerSeries
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Theorems.Thm_Wikipedia_SzemeredisTheorem_biUnion_cfzCanonicalCarryCell_eq_natBox

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









/-- `boxSum` is the usual sum over the literal finset `natBox`. -/
theorem boxSum_eq_sum_natBox {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (side : ι → ℕ) (F : (ι → ℕ) → A) :
    boxSum side F = ∑ x ∈ natBox side, F x := by
  rw [← Finset.sum_coe_sort]
  exact Fintype.sum_equiv (finiteBoxEquivNatBox side)
    (fun x : FiniteBox side ↦ F (fun i ↦ x i))
    (fun x : ↥(natBox side) ↦ F x)
    (fun _ ↦ rfl)

/-! ## Coordinatewise periodicity and exact box sums -/



























/-! ## Exact means -/









/-! ## Trimming and explicit boundary loss -/































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



/-- Distinct carry vectors have disjoint canonical cells. -/
theorem disjoint_cfzCanonicalCarryCell
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    {carry₁ carry₂ : κ → ℤ}
    (hne : carry₁ ≠ carry₂) :
    Disjoint
      (cfzCanonicalCarryCell (N := N) forms carry₁)
      (cfzCanonicalCarryCell (N := N) forms carry₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  have h₁ :=
    (mem_cfzCanonicalCarryCell (N := N) forms carry₁ x).mp hx₁
  have h₂ :=
    (mem_cfzCanonicalCarryCell (N := N) forms carry₂ x).mp hx₂
  exact hne (h₁.2.symm.trans h₂.2)



/-! ## Exact partition identities -/



/-- The family of canonical cells is pairwise disjoint on the finite carry
range. -/
theorem pairwise_disjoint_cfzCanonicalCarryCell
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k) :
    ((cfzCanonicalCarryVectorChoices κ k : Finset (κ → ℤ)) :
        Set (κ → ℤ)).Pairwise
      (fun carry₁ carry₂ =>
        Disjoint
          (cfzCanonicalCarryCell (N := N) forms carry₁)
          (cfzCanonicalCarryCell (N := N) forms carry₂)) := by
  intro carry₁ _hcarry₁ carry₂ _hcarry₂ hne
  exact disjoint_cfzCanonicalCarryCell (N := N) forms hne

/-- Every finite sum on the natural box decomposes exactly into the
divisor-independent canonical carry cells. -/
theorem sum_cfzCanonicalCarryCell_eq_sum_natBox
    {κ A : Type*} [Fintype κ] [DecidableEq κ]
    [AddCommMonoid A]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (F : (CFZVariable k → ℕ) → A) :
    ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        ∑ x ∈ cfzCanonicalCarryCell (N := N) forms carry,
          F x =
      ∑ x ∈ natBox (fun _ : CFZVariable k => N), F x := by
  rw [← biUnion_cfzCanonicalCarryCell_eq_natBox (N := N) forms]
  exact
    (Finset.sum_biUnion (M := A) (f := F)
      (pairwise_disjoint_cfzCanonicalCarryCell (N := N) forms)).symm

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Polylogarithmic growth of the canonical Rankin mass

The canonical coordinatewise-truncation estimate leaves a sharp arithmetic
Rankin mass.  This file proves that mass grows only polylogarithmically in
the selected CFZ, primorial, and reduced-residue regime.

There are two contributions.

* In the coordinatewise-truncated fibers, every divisor phase has norm at
  most one.  Every nonempty good-prime support costs at least `1 / p`, while
  a support at a prime dividing the primorial has zero density.  The
  truncated contribution is therefore bounded by the existing harmonic-LCM
  Euler majorant.
* The unrestricted Rpow coefficient mass factors over primes.  Its empty
  local support contributes one.  The total coefficient weight of all
  supports is at most `4 ^ m`, where `m` is the number of selected forms,
  and every nonempty support again costs `1 / p`.

The canonical carry-cell densities are nonnegative and sum exactly to one,
so these bounds are uniform in the carry vector.  Finally the existing
Selberg-scale estimate supplies one additional logarithm per selected form.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology
open scoped BigOperators

/-! ## The canonical carry cells form a probability partition -/

/-- A canonical carry-cell density is its cardinality divided by the
cardinality of the ambient natural box. -/
theorem cfzCanonicalCarryCellDensity_eq_card_div
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) :
    cfzCanonicalCarryCellDensity (N := N) forms carry =
      ((cfzCanonicalCarryCell (N := N) forms carry).card : ℝ) /
        ∏ _v : CFZVariable k, (N : ℝ) := by
  unfold cfzCanonicalCarryCellDensity boxMean
  rw [boxSum_eq_sum_natBox]
  unfold cfzCanonicalCarryCell cfzCanonicalCarryIndicator
  simp





/-! ## Divisor phases and fixed-carry support densities -/











/-! ## The coordinatewise-truncated part -/





/-! ## The unrestricted Rpow part -/

















/-! ## Fixed-family and carry-averaged mass bounds -/







/-! ## Primorial polylogarithmic bounds -/



















end Wikipedia.SzemeredisTheorem

end
/-!
# Polylogarithmic growth of the canonical Rankin mass

The canonical coordinatewise-truncation estimate leaves a sharp arithmetic
Rankin mass.  This file proves that mass grows only polylogarithmically in
the selected CFZ, primorial, and reduced-residue regime.

There are two contributions.

* In the coordinatewise-truncated fibers, every divisor phase has norm at
  most one.  Every nonempty good-prime support costs at least `1 / p`, while
  a support at a prime dividing the primorial has zero density.  The
  truncated contribution is therefore bounded by the existing harmonic-LCM
  Euler majorant.
* The unrestricted Rpow coefficient mass factors over primes.  Its empty
  local support contributes one.  The total coefficient weight of all
  supports is at most `4 ^ m`, where `m` is the number of selected forms,
  and every nonempty support again costs `1 / p`.

The canonical carry-cell densities are nonnegative and sum exactly to one,
so these bounds are uniform in the carry vector.  Finally the existing
Selberg-scale estimate supplies one additional logarithm per selected form.
-/
open Wikipedia.SzemeredisTheorem
open Filter Topology
open scoped BigOperators
/-! ## The canonical carry cells form a probability partition -/

open Wikipedia.SzemeredisTheorem in
/-- The canonical carry-cell densities sum to one. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k) :
    ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        cfzCanonicalCarryCellDensity (N := N) forms carry = 1 := by
  simp_rw [cfzCanonicalCarryCellDensity_eq_card_div]
  rw [← Finset.sum_div]
  have hpartition :=
    sum_cfzCanonicalCarryCell_eq_sum_natBox
      (N := N) forms (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hpartition
  rw [hpartition, card_natBox, Nat.cast_prod]
  exact div_self (by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _hv
    exact_mod_cast (NeZero.ne N))
