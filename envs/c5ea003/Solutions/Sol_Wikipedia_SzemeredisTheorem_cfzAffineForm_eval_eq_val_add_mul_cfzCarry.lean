-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cfzAffineForm_eval_eq_val_add_mul_cfzCarry
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:46:33.47999+00:00
-- url     : https://prove2.me/submissions/656f5861-7681-4f29-8419-f5b68b3db667

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cfzCoefficientEval_eq_apLinearForm

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







/-- The integer CFZ form evaluated on natural representatives represents
the cyclic CFZ form modulo `N`. -/
theorem intCast_cfzAffineForm_eval_eq_apLinearForm
    {k N : ℕ}
    (q : CFZFormIndex k) (x : CFZVariable k → ℕ) :
    (((cfzAffineForm q).eval
        (fun v => (x v : ℤ)) : ℤ) : ZMod N) =
      apLinearForm k N q.1 q.2
        (cubePointOfNat (N := N) x) := by
  rw [← cfzCoefficientEval_eq_apLinearForm k N q]
  unfold cfzCoefficientEval
  simp only [AffineForm.eval, cfzAffineForm_constant,
    cfzAffineForm_coefficient, zero_add]
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Why cyclic representatives need a compatibility or carry argument -/
/-! ## Weighted lifts through two moduli -/
/-! ## Natural representatives of CFZ cube points -/
/-! ## Canonical carry cells -/

open Wikipedia.SzemeredisTheorem in
/-- The standard representative of the cyclic form plus `N` times the
canonical carry is exactly the original integer affine evaluation. -/
theorem solution
    {k N : ℕ} [NeZero N]
    (q : CFZFormIndex k) (x : CFZVariable k → ℕ) :
    (cfzAffineForm q).eval (fun v => (x v : ℤ)) =
      (apLinearForm k N q.1 q.2
        (cubePointOfNat (N := N) x)).val +
        (N : ℤ) * cfzCarry (N := N) q x := by
  let A : ℤ :=
    (cfzAffineForm q).eval (fun v => (x v : ℤ))
  let a : ZMod N :=
    apLinearForm k N q.1 q.2
      (cubePointOfNat (N := N) x)
  have hcast : (A : ZMod N) = a := by
    exact intCast_cfzAffineForm_eval_eq_apLinearForm q x
  have hval : (a.val : ℤ) = A % (N : ℤ) := by
    calc
      (a.val : ℤ) = (((A : ZMod N).val : ℕ) : ℤ) := by
        exact_mod_cast congrArg ZMod.val hcast.symm
      _ = A % (N : ℤ) := ZMod.val_intCast A
  change A = (a.val : ℤ) + (N : ℤ) * (A / (N : ℤ))
  rw [hval]
  exact (Int.emod_add_mul_ediv A (N : ℤ)).symm
