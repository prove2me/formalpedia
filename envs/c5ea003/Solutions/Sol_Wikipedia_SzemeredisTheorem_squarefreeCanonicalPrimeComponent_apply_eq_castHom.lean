-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.squarefreeCanonicalPrimeComponent_apply_eq_castHom
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:45:14.949468+00:00
-- url     : https://prove2.me/submissions/a8fbb0dc-bd65-42a6-ba57-85f05189012a

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
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
# Exact squarefree CRT products for selected CFZ affine families

This file connects the natural representative
`cfzWTrickedAffineResidueValue` to the canonical squarefree CRT interface in
`PairedLocalFactors`.  The resulting factorization is exact for every finite
reindexing of the CFZ family, and hence for every selected CFZ family.

The prime factors are then specialized in the two regimes needed by the
W-trick.  At primes dividing `W`, reduced residues make every nonempty
common-zero density vanish.  At primes outside `W` and above the ambient
CFZ exceptional cutoff, direct modular good-prime geometry gives the exact
empty, singleton, and pair densities and the uniform `p⁻²` bound for every
nontrivial support.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## The squarefree CRT component is ordinary reduction modulo `p` -/

/-- Casting a vector of residues along an equality of moduli is the
coordinatewise cast. -/
theorem equivCast_zmodPi_apply
    {ι : Type*} {m n : ℕ} (h : m = n)
    (x : ι → ZMod m) (i : ι) :
    Equiv.cast (congrArg (fun d => ι → ZMod d) h) x i =
      Equiv.cast (congrArg ZMod h) (x i) := by
  subst n
  rfl

/-- The type-theoretic cast between two equal `ZMod` moduli agrees with the
canonical congruence ring equivalence. -/
theorem equivCast_zmod_eq_ringEquivCongr
    {m n : ℕ} (h : m = n) (x : ZMod m) :
    Equiv.cast (congrArg ZMod h) x =
      ZMod.ringEquivCongr h x := by
  subst n
  simp



/-! ## The exact natural-valued affine prime model -/





/-! ## Exact CRT products for arbitrary finite and selected CFZ families -/





/-! ## Prime factors dividing `W` -/







/-! ## Prime factors outside `W` above the ambient CFZ cutoff -/















end Wikipedia.SzemeredisTheorem

end
/-!
# Exact squarefree CRT products for selected CFZ affine families

This file connects the natural representative
`cfzWTrickedAffineResidueValue` to the canonical squarefree CRT interface in
`PairedLocalFactors`.  The resulting factorization is exact for every finite
reindexing of the CFZ family, and hence for every selected CFZ family.

The prime factors are then specialized in the two regimes needed by the
W-trick.  At primes dividing `W`, reduced residues make every nonempty
common-zero density vanish.  At primes outside `W` and above the ambient
CFZ exceptional cutoff, direct modular good-prime geometry gives the exact
empty, singleton, and pair densities and the uniform `p⁻²` bound for every
nontrivial support.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## The squarefree CRT component is ordinary reduction modulo `p` -/

open Wikipedia.SzemeredisTheorem in
/-- On each coordinate, the canonical squarefree CRT component is ordinary
reduction from the global modulus to the underlying prime. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    {z : κ → ℕ × ℕ}
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors)
    (x : ι → ZMod (pairedDivisorLcm z))
    (i : ι) :
    squarefreeCanonicalPrimeComponent hz p x i =
      ZMod.castHom (Nat.dvd_of_mem_primeFactors p.2)
        (ZMod (p : ℕ)) (x i) := by
  classical
  let : NeZero (pairedDivisorLcm z) :=
    ⟨(squarefree_pairedDivisorLcm hz).ne_zero⟩
  let hpow :
      (p : ℕ) ^ (pairedDivisorLcm z).factorization p = p :=
    pairedDivisorLcm_primePower_eq_prime hz p
  have htransport :
      squarefreePrimePowerEquiv hz p
          (coordinatePrimePowerEquiv x p) i =
        (ZMod.ringEquivCongr hpow).toFun
          (coordinatePrimePowerEquiv x p i) := by
    unfold squarefreePrimePowerEquiv
    change
      Equiv.cast
          (congrArg (fun d => ι → ZMod d) hpow)
          (coordinatePrimePowerEquiv x p) i =
        (ZMod.ringEquivCongr hpow).toFun
          (coordinatePrimePowerEquiv x p i)
    rw [equivCast_zmodPi_apply,
      equivCast_zmod_eq_ringEquivCongr]
    · rfl
    all_goals exact hpow
  rw [show
      squarefreeCanonicalPrimeComponent hz p x i =
        squarefreePrimePowerEquiv hz p
          (coordinatePrimePowerEquiv x p) i by
      rfl,
    htransport]
  change
    (ZMod.ringEquivCongr hpow).toFun
        (ZMod.equivPi (pairedDivisorLcm z)
          (NeZero.ne (pairedDivisorLcm z)) (x i) p) =
      ZMod.castHom (Nat.dvd_of_mem_primeFactors p.2)
        (ZMod (p : ℕ)) (x i)
  let componentHom : ZMod (pairedDivisorLcm z) →+* ZMod (p : ℕ) :=
    (ZMod.ringEquivCongr hpow).toRingHom.comp
      ((Pi.evalRingHom
        (fun r : (pairedDivisorLcm z).primeFactors =>
          ZMod ((r : ℕ) ^
            (pairedDivisorLcm z).factorization r)) p).comp
        (ZMod.equivPi (pairedDivisorLcm z)
          (NeZero.ne (pairedDivisorLcm z))).toRingHom)
  have hhom :
      componentHom =
        ZMod.castHom (Nat.dvd_of_mem_primeFactors p.2)
          (ZMod (p : ℕ)) :=
    Subsingleton.elim _ _
  simpa [componentHom] using
    RingHom.congr_fun hhom (x i)
