-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.sum_cfzCanonicalCarryCellCyclicContribution_eq_density
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:45:55.830278+00:00
-- url     : https://prove2.me/submissions/be0ba54a-0258-458c-9aa1-bd169eae79ac

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_biUnion_cfzCanonicalCarryCell_eq_natBox
import Theorems.Thm_Wikipedia_SzemeredisTheorem_boxMean_cfzCanonicalCarryIndicator_mul_eq_cellSum_div

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





/-- A mean on the cyclic CFZ cube is exactly the natural-box mean of its
standard-representative pullback. -/
theorem mean_cubePoint_eq_boxMean
    {k N : ℕ} [NeZero N]
    (F : CubePoint k N → ℝ) :
    mean F =
      boxMean (fun _ : CFZVariable k => N)
        (fun x => F (cubePointOfNat (N := N) x)) := by
  rw [boxMean_eq_mean_finiteBox]
  symm
  unfold mean
  apply Fintype.expect_equiv (finiteBoxEquivCubePoint k N)
  intro x
  rfl

/-! ## CFZ periodicity under lift compatibility -/







/-! ## The exact affine residue model -/













/-! ## Normalized trimming loss -/







/-! ## Paired divisibility specialization -/









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
/-! ## Exact residue mean and CRT product -/
/-! ## Per-cell cyclic-to-Euler comparison -/
/-! ## Summing the canonical carry cells -/

open Wikipedia.SzemeredisTheorem in
/-- The original cyclic paired divisibility density is the exact sum of its
canonical carry-cell contributions. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b : ℕ)
    (forms : κ → CFZFormIndex k)
    (z : κ → ℕ × ℕ) :
    ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        cfzCanonicalCarryCellCyclicContribution
          (N := N) W b forms carry z =
      pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z := by
  let F : (CFZVariable k → ℕ) → ℝ :=
    fun x =>
      pairedDivisibilityIndicator
        (fun q y =>
          cfzWTrickedLinearValue W b (forms q)
            (cubePointOfNat (N := N) y))
        z x
  have hcell :
      ∀ carry : κ → ℤ,
        cfzCanonicalCarryCellCyclicContribution
            (N := N) W b forms carry z =
          (∑ x ∈ cfzCanonicalCarryCell
              (N := N) forms carry, F x) /
            ∏ _v : CFZVariable k, (N : ℝ) := by
    intro carry
    unfold cfzCanonicalCarryCellCyclicContribution
    exact
      boxMean_cfzCanonicalCarryIndicator_mul_eq_cellSum_div
        forms carry F
  calc
    ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        cfzCanonicalCarryCellCyclicContribution
          (N := N) W b forms carry z =
        ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
          (∑ x ∈ cfzCanonicalCarryCell
              (N := N) forms carry, F x) /
            ∏ _v : CFZVariable k, (N : ℝ) := by
      apply Finset.sum_congr rfl
      intro carry _hcarry
      exact hcell carry
    _ =
        (∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
          ∑ x ∈ cfzCanonicalCarryCell
              (N := N) forms carry, F x) /
            ∏ _v : CFZVariable k, (N : ℝ) := by
      symm
      rw [Finset.sum_div]
    _ = (∑ x ∈ natBox
            (fun _ : CFZVariable k => N), F x) /
          ∏ _v : CFZVariable k, (N : ℝ) := by
      rw [sum_cfzCanonicalCarryCell_eq_sum_natBox
        (N := N) forms F]
    _ = boxMean (fun _ : CFZVariable k => N) F := by
      rw [boxMean, boxSum_eq_sum_natBox]
    _ = pairedDivisibilityDensity
        (fun q (x : CubePoint k N) =>
          cfzWTrickedLinearValue W b (forms q) x)
        z := by
      unfold pairedDivisibilityDensity
      rw [mean_cubePoint_eq_boxMean]
      rfl
