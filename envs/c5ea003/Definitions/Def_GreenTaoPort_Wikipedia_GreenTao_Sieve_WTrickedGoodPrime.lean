-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:05:34.695827+00:00
-- url     : https://prove2.me/theorems/7e1ba9f5-3aad-42d9-a4b0-e58c12d18311
-- title:
--   Modular nonvanishing and a uniform CFZ exceptional cutoff
-- statement:
--   For integer affine forms $(\psi_q)$ on a finite variable type, the nonzero-good-prime predicate requires a prime $p$ and, for each form index $q$, at least one coefficient that remains nonzero modulo $p$. This is a direct modular condition, stronger than merely writing down a nonzero integer coefficient vector without controlling the modulus.
--
--   The bundle also fixes one natural exceptional cutoff for the full CFZ system at progression length $k$. It is the maximum of the explicit coefficient-and-minor bound and the complex zeta-model nonvanishing cutoff at the full form-family cardinality. It is chosen before any $W$-scaling or subfamily selection.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/WTrickedGoodPrime.lean#L37-L675

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
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

/-- Every form has a nonzero linear coefficient modulo the prime `p`.
Unlike `NonzeroCoefficientVectors`, this is a direct modular assertion. -/
def AffineNonzeroGoodPrime
    {κ ι : Type*} [Fintype ι]
    (p : ℕ) (forms : κ → AffineForm ι ℤ) : Prop :=
  p.Prime ∧
    ∀ q : κ, ∃ i : ι,
      ((forms q).coefficient i : ZMod p) ≠ 0







/-! ## Scaling identities and W-trick preservation -/

















/-! ## Exact one- and two-form densities -/









/-! ## Complex first-order expansion from modular geometry -/





/-! ## Stable complex and paired-Fourier ratios -/







/-! ## Direct comparison with the zeta Euler model -/





/-! ## Uniform selected-CFZ specialization -/









/-- A single exceptional cutoff for every selected CFZ subfamily.  It is
computed from the original full CFZ family, before W-scaling, and hence
depends only on `k`. -/
def wTrickedCFZComplexExceptionalBound (k : ℕ) : ℕ :=
  max
    (exceptionalPrimeBound
      (fun q : CFZFormIndex k => cfzAffineForm q))
    (complexZetaModelNonzeroCutoff
      (Fintype.card (CFZFormIndex k)))















end Wikipedia.SzemeredisTheorem


