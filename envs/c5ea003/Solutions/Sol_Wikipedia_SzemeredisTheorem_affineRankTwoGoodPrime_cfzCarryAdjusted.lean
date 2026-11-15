-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.affineRankTwoGoodPrime_cfzCarryAdjusted
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:44:20.4038+00:00
-- url     : https://prove2.me/submissions/d638be65-e405-4be4-bb20-42d76806d49b

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
# Large-prime geometry for W-tricked affine systems

The integer exceptional-prime bound of a system scales with `W` after
replacing every form `ψ` by `W * ψ + b`.  That bound is therefore the wrong
interface for the large primes in the W-tricked Euler product.  Modulo a
prime `p ∤ W`, multiplication by `W` is a unit.  Consequently:

* a nonzero coefficient modulo `p` stays nonzero;
* every nonzero two-by-two coefficient minor stays nonzero, since the minor
  is multiplied by `W²`;
* affine constants play no role in either assertion and may vary from form
  to form.

This file packages that observation as direct modular good-prime predicates,
derives the exact one- and two-form densities without applying an exceptional
bound to the transformed integer system, and rebuilds the complex
paired-Fourier local-factor estimates from those modular hypotheses.

The final results apply uniformly to every subtype `SelectedCFZFormIndex e`.
Their exceptional cutoff depends only on the ambient CFZ parameter `k`.
The W-trick contributes only the natural hypothesis `p ∤ W`; neither the
size of `W` nor any (possibly carry-dependent) affine constant enters the
cutoff.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Modular one-form geometry -/









/-! ## Scaling identities and W-trick preservation -/

/-- A W-trick multiplies every coefficient minor by `W²`.  The two affine
constants do not occur in this identity. -/
@[simp]
theorem wTrickedAffineForm_coefficientMinor
    {ι : Type*} (W b c : ℕ)
    (ψ φ : AffineForm ι ℤ) (i j : ι) :
    (wTrickedAffineForm W b ψ).coefficientMinor
        (wTrickedAffineForm W c φ) i j =
      (W : ℤ) ^ 2 * ψ.coefficientMinor φ i j := by
  simp only [AffineForm.coefficientMinor,
    wTrickedAffineForm_coefficient]
  ring

/-- At a modulus not dividing `W`, its residue class is nonzero. -/
theorem natCast_zmod_ne_zero_of_not_dvd
    {W p : ℕ} (hpW : ¬p ∣ W) :
    (W : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact hpW



/-- A nonzero modular minor survives W-scaling, uniformly in the two affine
constants. -/
theorem wTrickedAffineForm_coefficientMinor_cast_ne_zero
    {ι : Type*} {W b c p : ℕ} (hp : p.Prime)
    (hpW : ¬p ∣ W) (ψ φ : AffineForm ι ℤ)
    {i j : ι}
    (hij : (ψ.coefficientMinor φ i j : ZMod p) ≠ 0) :
    ((wTrickedAffineForm W b ψ).coefficientMinor
        (wTrickedAffineForm W c φ) i j : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [wTrickedAffineForm_coefficientMinor]
  push_cast
  exact mul_ne_zero
    (pow_ne_zero 2 (natCast_zmod_ne_zero_of_not_dvd hpW))
    hij









/-! ## Exact one- and two-form densities -/









/-! ## Complex first-order expansion from modular geometry -/





/-! ## Stable complex and paired-Fourier ratios -/







/-! ## Direct comparison with the zeta Euler model -/





/-! ## Uniform selected-CFZ specialization -/

























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













@[simp]
theorem cfzCarryAdjustedAffineForm_coefficient
    {k : ℕ} (N W b : ℕ)
    (q : CFZFormIndex k) (c : ℤ)
    (v : CFZVariable k) :
    (cfzCarryAdjustedAffineForm N W b q c).coefficient v =
      (W : ℤ) * cfzCoefficient q v := by
  rfl

















/-! ## A normalized disagreement bound -/





















/-! ## Carry-dependent affine residue model -/















end Wikipedia.SzemeredisTheorem

end

section




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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A generic natural representative for an affine residue -/









/-! ## Complete quotient blocks and their affine families -/









/-! ## Good complete quotient blocks -/













/-! ## Exact blockwise CRT and averaged Euler products -/







/-! ## The complete-block mean is the averaged Euler product -/



/-! ## The outer partial-block boundary -/







/-! ## Unconditional cyclic-to-Euler approximation -/









/-! ## Selected-family specialization -/









/-! ## Carry-dependent constants and primes dividing `W` -/



















/-! ## Good primes outside `W` -/

/-- Carry corrections change only affine constants.  Every coefficient
minor is still scaled by `W²`. -/
@[simp]
theorem cfzCarryAdjustedAffineForm_coefficientMinor
    {k : ℕ} (N W b : ℕ)
    (q r : CFZFormIndex k) (c d : ℤ)
    (i j : CFZVariable k) :
    (cfzCarryAdjustedAffineForm N W b q c).coefficientMinor
        (cfzCarryAdjustedAffineForm N W b r d) i j =
      (W : ℤ) ^ 2 *
        (cfzAffineForm q).coefficientMinor
          (cfzAffineForm r) i j := by
  simp only [AffineForm.coefficientMinor,
    cfzCarryAdjustedAffineForm_coefficient,
    cfzAffineForm_coefficient]
  ring

















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
/-! ## Unconditional cyclic-to-Euler approximation -/
/-! ## Selected-family specialization -/
/-! ## Carry-dependent constants and primes dividing `W` -/
/-! ## Good primes outside `W` -/

open Wikipedia.SzemeredisTheorem in
/-- Direct modular rank-two geometry likewise survives arbitrary
carry-dependent constants whenever `p ∤ W`. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {k p : ℕ}
    (N W b : ℕ) (forms : κ → CFZFormIndex k)
    (c : κ → ℤ)
    (hgood : AffineRankTwoGoodPrime p
      (fun q => cfzAffineForm (forms q)))
    (hpW : ¬p ∣ W) :
    AffineRankTwoGoodPrime p
      (fun q =>
        cfzCarryAdjustedAffineForm
          N W b (forms q) (c q)) := by
  refine ⟨hgood.1, ?_⟩
  intro q r hqr
  obtain ⟨i, j, hij⟩ := hgood.2 hqr
  refine ⟨i, j, ?_⟩
  have hw :=
    wTrickedAffineForm_coefficientMinor_cast_ne_zero
      (W := W) (b := 0) (c := 0) (p := p)
      hgood.1 hpW
      (cfzAffineForm (forms q))
      (cfzAffineForm (forms r)) hij
  simpa only [cfzCarryAdjustedAffineForm_coefficientMinor,
    wTrickedAffineForm_coefficientMinor] using hw
