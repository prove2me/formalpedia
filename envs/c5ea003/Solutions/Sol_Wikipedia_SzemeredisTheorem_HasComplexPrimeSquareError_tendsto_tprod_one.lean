-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HasComplexPrimeSquareError.tendsto_tprod_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:39:54.111196+00:00
-- url     : https://prove2.me/submissions/07055dd9-026c-40a7-9c49-9e2274c90505

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
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
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Euler-product control from square-decaying local errors

The good-prime calculation for the Green--Tao linear-forms system produces
local factors of the form `1 + O(p⁻²)`, outside a finite exceptional set.
This file packages the analytic consequence which is independent of the
particular local-factor formula.

The series of reciprocal prime squares is summable.  Consequently a local
factor with error at most `C / p²` has an absolutely summable error, its
Euler product is multipliable, every finite partial product has an explicit
exponential error bound, and products supported sufficiently far out in the
prime tail are arbitrarily close to one.  A masked version records the
standard operation of replacing finitely many exceptional local factors by
one.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Reciprocal squares are summable over the subtype of natural primes. -/
theorem summable_prime_inv_sq :
    Summable
      (fun p : Nat.Primes =>
        (1 : ℝ) / (p : ℝ) ^ 2) := by
  have h :
      Summable
        (fun p : Nat.Primes =>
          (p : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  refine h.congr fun p => ?_
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [one_div]



namespace HasPrimeSquareError





















end HasPrimeSquareError

/-! ## Removing finitely many exceptional primes -/











/-! ## Masking by a numerical cutoff -/









end Wikipedia.SzemeredisTheorem

end

section



/-!
# Complex good-prime local factors after Fourier inversion

Fourier inversion turns each of the two smooth divisor sums attached to a
form into a complex multiplicative phase.  At a prime `p`, if the two phases
are `z` and `w`, the four squarefree divisor choices contribute

`1 - (z + w - z * w) 1_{p ∣ ψ(x)}`.

Thus the arithmetic local factor is a complex-weighted avoidance average.
This file develops that average directly over `ℂ`, proves its exact finite
inclusion--exclusion expansion, and isolates the singleton contribution.
At a rank-two good prime the remaining supports have density at most
`p⁻²`, so the complex remainder is bounded by the product of
`1 + ‖a q‖`.

For the Fourier coefficients, every divisor phase has norm at most one when
`R ≥ 2`, hence `‖z + w - z * w‖ ≤ 3`.  Consequently the higher-order
coefficient mass is at most `4 ^ m` for a system of `m` forms.  Above
`p ≥ 6m`, the complex first-order model has norm at least `1/2`; division by
that model therefore gives the explicit ratio estimate

`‖localRatio p - 1‖ ≤ 2 * 4 ^ m / p²`.

The final CFZ theorem masks the finite exceptional range and packages these
ratios in a complex analogue of `HasPrimeSquareError`, including
multipliability of the resulting remainder Euler product.

This does not yet compare the first-order model with the local factors of
the appropriate multivariate zeta quotient.  That analytic comparison, and
the subsequent parameter-uniform integration, are separate steps.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Complex finite averages -/









/-! ## Exact complex inclusion--exclusion -/















/-! ## Norm bounds for the complex remainder -/













/-! ## A stable complex first-order ratio -/









/-! ## Fourier phase coefficients -/

namespace SmoothSieveCutoff





end SmoothSieveCutoff

























/-! ## Complex square-error Euler-product interface -/



namespace HasComplexPrimeSquareError



theorem error_le
    {C : ℝ} {localFactor : Nat.Primes → ℂ}
    (h : HasComplexPrimeSquareError C localFactor)
    (p : Nat.Primes) :
    ‖localFactor p - 1‖ ≤ C / (p : ℝ) ^ 2 :=
  h.2 p







end HasComplexPrimeSquareError









/-! ## CFZ specialization -/















end Wikipedia.SzemeredisTheorem

end
/-!
# Uniform tails of complex Euler products

The local estimates used in the smooth sieve are uniform in the Fourier
variables but the local-factor family itself changes with all asymptotic
parameters.  Ordinary convergence of one fixed Euler product is therefore
not enough.

This file packages the required dominated-convergence statement.  If a
varying family has the common bound

`‖L_n(p) - 1‖ ≤ C / p²`

and each fixed prime factor tends to one, then the full unordered products
also tend to one.  A second theorem specializes this to the standard
large-prime mask: all factors at `p ≤ w_n` are replaced by one, and
`w_n → ∞`.  No bound on the Fourier variables is needed because the local
square-error estimate is already uniform in them.
-/
open Wikipedia.SzemeredisTheorem
open Filter Topology
open Wikipedia.SzemeredisTheorem.HasComplexPrimeSquareError

open Wikipedia.SzemeredisTheorem.HasComplexPrimeSquareError in
/-- Dominated convergence for a varying family of complex Euler products
with one common prime-square error majorant. -/
theorem solution
    {α : Type*} {𝓕 : Filter α}
    {C : ℝ} {localFactor : α → Nat.Primes → ℂ}
    (herror :
      ∀ᶠ n in 𝓕,
        HasComplexPrimeSquareError C (localFactor n))
    (hpoint :
      ∀ p : Nat.Primes,
        Tendsto (fun n => localFactor n p)
          𝓕 (𝓝 1)) :
    Tendsto
      (fun n => ∏' p : Nat.Primes, localFactor n p)
      𝓕 (𝓝 1) := by
  have hsum :
      Summable
        (fun p : Nat.Primes =>
          C / (p : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      summable_prime_inv_sq.mul_left C
  have hpointError :
      ∀ p : Nat.Primes,
        Tendsto
          (fun n => localFactor n p - 1)
          𝓕 (𝓝 0) := by
    intro p
    simpa using
      (hpoint p).sub
        (tendsto_const_nhds :
          Tendsto (fun _n : α => (1 : ℂ)) 𝓕 (𝓝 1))
  have hbound :
      ∀ᶠ n in 𝓕, ∀ p : Nat.Primes,
        ‖localFactor n p - 1‖ ≤
          C / (p : ℝ) ^ 2 :=
    herror.mono fun _n hn p => hn.error_le p
  simpa using
    (tendsto_tprod_one_add_of_dominated_convergence
      (R := ℂ)
      (g := fun _p : Nat.Primes => 0)
      hsum hpointError hbound)
