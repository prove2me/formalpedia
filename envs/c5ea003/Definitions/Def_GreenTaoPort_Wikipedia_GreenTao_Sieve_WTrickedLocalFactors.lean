-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:03:59.326359+00:00
-- url     : https://prove2.me/theorems/c2607ba7-df13-42d1-98d8-cd5a658d34be
-- title:
--   The integer affine W-trick
-- statement:
--   For natural parameters $W,b$ and an integer affine form $\psi(x)=c+\sum_i a_i x_i$, its $W$-tricked form is
--
--   $$
--   \psi_{W,b}(x)=W\psi(x)+b.
--   $$
--
--   Thus its constant is $Wc+b$ and its coefficient at $i$ is $Wa_i$, with natural parameters cast to integers. The construction itself requires neither $W>0$ nor a coprimality condition on $b$; those assumptions are supplied when evaluating the later local factors.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/WTrickedLocalFactors.lean#L23-L28

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


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

/-- The integer affine form obtained from `ψ` by the `W`-trick:
`x ↦ W * ψ(x) + b`. -/
def wTrickedAffineForm {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) : AffineForm ι ℤ where
  constant := (W : ℤ) * ψ.constant + b
  coefficient i := (W : ℤ) * ψ.coefficient i































end Wikipedia.SzemeredisTheorem


