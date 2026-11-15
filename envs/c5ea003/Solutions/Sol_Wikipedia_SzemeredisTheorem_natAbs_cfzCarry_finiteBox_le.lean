-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.natAbs_cfzCarry_finiteBox_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:22:29.090632+00:00
-- url     : https://prove2.me/submissions/656753ec-ad69-45dd-bad1-9224f0066411

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cfzAffineForm_eval_eq_val_add_mul_cfzCarry
import Theorems.Thm_Wikipedia_SzemeredisTheorem_natAbs_cfzAffineForm_eval_finiteBox_le

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
/-- Consequently the canonical carry on the standard box ranges over a
fixed finite interval depending only on `k`. -/
theorem solution
    {k N : ℕ} [NeZero N]
    (q : CFZFormIndex k)
    (x : FiniteBox (fun _ : CFZVariable k => N)) :
    Int.natAbs
        (cfzCarry (N := N) q (fun v => (x v : ℕ))) ≤
      Fintype.card (CFZVariable k) * k + 1 := by
  let xNat : CFZVariable k → ℕ := fun v => (x v : ℕ)
  let A : ℤ :=
    (cfzAffineForm q).eval (fun v => (xNat v : ℤ))
  let a : ZMod N :=
    apLinearForm k N q.1 q.2
      (cubePointOfNat (N := N) xNat)
  let c : ℤ := cfzCarry (N := N) q xNat
  have hidentity : A = (a.val : ℤ) + (N : ℤ) * c := by
    exact cfzAffineForm_eval_eq_val_add_mul_cfzCarry q xNat
  have hdiff : A - (a.val : ℤ) = (N : ℤ) * c := by
    rw [hidentity]
    ring
  have habs :
      Int.natAbs (A - (a.val : ℤ)) =
        N * Int.natAbs c := by
    rw [hdiff, Int.natAbs_mul, Int.natAbs_natCast]
  have hA :
      Int.natAbs A ≤
        Fintype.card (CFZVariable k) * k * N := by
    exact natAbs_cfzAffineForm_eval_finiteBox_le q x
  have ha : a.val ≤ N := (ZMod.val_lt a).le
  have hdiffBound :
      Int.natAbs (A - (a.val : ℤ)) ≤
        N * (Fintype.card (CFZVariable k) * k + 1) := by
    calc
      Int.natAbs (A - (a.val : ℤ)) ≤
          Int.natAbs A + Int.natAbs (a.val : ℤ) :=
        Int.natAbs_sub_le _ _
      _ = Int.natAbs A + a.val := by
        rw [Int.natAbs_natCast]
      _ ≤ Fintype.card (CFZVariable k) * k * N + N :=
        Nat.add_le_add hA ha
      _ = N * (Fintype.card (CFZVariable k) * k + 1) := by
        ring
  apply Nat.le_of_mul_le_mul_left
    (show
      N * Int.natAbs c ≤
        N * (Fintype.card (CFZVariable k) * k + 1) by
      rw [← habs]
      exact hdiffBound)
    (NeZero.pos N)
