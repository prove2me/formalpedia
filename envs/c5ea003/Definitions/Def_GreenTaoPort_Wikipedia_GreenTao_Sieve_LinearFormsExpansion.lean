-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:54:49.672203+00:00
-- url     : https://prove2.me/theorems/acb36dbe-cb38-410a-925f-27e5fa6a58db
-- title:
--   Finite paired-divisor data for the Selberg expansion
-- statement:
--   At a natural sieve level $R$, divisor choices lie in $\{1,\ldots,R\}$; a Selberg square supplies a pair of such choices, and a finite form family supplies one pair per index. The Möbius-cutoff coefficient is the product, over all indices, of the two individual smooth divisor summands.
--
--   Given natural-valued form evaluations, the paired divisibility indicator is the product of the zero–one indicators that both chosen divisors divide each evaluation. Its normalized mean over a finite sample space is the paired divisibility density. The bundle also supplies the least common multiple of every chosen divisor and the normalization scalar $\varphi(W)/(Wc_\chi\log R)$.
--
--   For CFZ forms on a positive cyclic modulus, the natural $W$-tricked lift is $W$ times the standard representative of the form value plus the residue shift $b$. The finite-choice definitions remain total when the sieve level or other natural parameters are degenerate.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/LinearFormsExpansion.lean#L35-L444

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Exact finite expansion of Selberg weights along linear forms

This file performs the algebraic expansion that precedes the analytic
Goldston--Yıldırım estimate.  For a finite family of positive
natural-valued forms, the mean of a product of smooth Selberg squares is
written exactly as a finite sum over two bounded divisor choices per form.
Each term splits into

* a product of smooth Möbius-cutoff coefficients; and
* the exact density of the simultaneous divisibility congruences.

The least common multiple of the chosen divisors is bounded by
`R ^ (2 * card κ)`, using `CongruenceAverage`.  The final section
specializes the identity to the full CFZ family evaluated through
`apLinearForm` and the natural W-tricked lift.

There are no asymptotic estimates here.  Factoring the composite-modulus
congruence density into prime local factors, controlling the exceptional
primes, and bounding the resulting Euler product remain separate analytic
steps.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Bounded divisor choices and congruence densities -/

/-- Positive divisor choices allowed by a cutoff at `R`. -/
def smoothDivisorChoices (R : ℕ) : Finset ℕ :=
  Finset.Icc 1 R

/-- The pair of divisor choices created by one Selberg square. -/
def smoothDivisorPairChoices (R : ℕ) :
    Finset (ℕ × ℕ) :=
  (smoothDivisorChoices R).product
    (smoothDivisorChoices R)

/-- A simultaneous pair of divisor choices for every member of a finite
family. -/
def smoothDivisorFamilyChoices
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (R : ℕ) :
    Finset (κ → ℕ × ℕ) :=
  Fintype.piFinset fun _ : κ =>
    smoothDivisorPairChoices R

/-- Real-valued indicator of the natural divisibility relation. -/
def natDivisibilityIndicator (d n : ℕ) : ℝ :=
  if d ∣ n then 1 else 0

/-- The smooth Möbius coefficient attached to a family of paired divisor
choices. -/
noncomputable def smoothDivisorFamilyCoefficient
    {κ : Type*} [Fintype κ]
    (χ : ℝ → ℝ) (R : ℕ)
    (z : κ → ℕ × ℕ) : ℝ :=
  ∏ q,
    smoothDivisorSummand χ R (z q).1 *
      smoothDivisorSummand χ R (z q).2

/-- Indicator of all paired divisor conditions in one expansion term. -/
def pairedDivisibilityIndicator
    {κ X : Type*} [Fintype κ]
    (values : κ → X → ℕ)
    (z : κ → ℕ × ℕ) (x : X) : ℝ :=
  ∏ q,
    natDivisibilityIndicator (z q).1 (values q x) *
      natDivisibilityIndicator (z q).2 (values q x)

/-- Exact finite density of the simultaneous paired divisor
congruences. -/
noncomputable def pairedDivisibilityDensity
    {κ X : Type*} [Fintype κ] [Fintype X]
    (values : κ → X → ℕ)
    (z : κ → ℕ × ℕ) : ℝ :=
  mean (pairedDivisibilityIndicator values z)

/-- LCM of the `2 * card κ` moduli in one divisor-choice term. -/
def pairedDivisorLcm
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ℕ × ℕ) : ℕ :=
  Finset.univ.lcm
    (Sum.elim (fun q => (z q).1)
      (fun q => (z q).2))





/-! ## One Selberg square -/







/-! ## A finite family of Selberg squares -/





/-! ## Normalized Selberg majorants -/

/-- Scalar relating the normalized Selberg majorant to its unnormalized
square. -/
noncomputable def normalizedSelbergScale
    (cχ : ℝ) (R W : ℕ) : ℝ :=
  ((W.totient : ℝ) / W) /
    (cχ * Real.log R)





/-! ## CFZ specialization -/

/-- The positive natural W-tricked lift of one CFZ residue-valued linear
form. -/
def cfzWTrickedLinearValue
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (q : CFZFormIndex k)
    (x : CubePoint k N) : ℕ :=
  wTrickedValue W b
    (apLinearForm k N q.1 q.2 x)







end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cfzWTrickedLinearValue.congr_simp,
    `Wikipedia.SzemeredisTheorem.natDivisibilityIndicator.eq_1,
    `Wikipedia.SzemeredisTheorem.pairedDivisorLcm.eq_1,
    `Wikipedia.SzemeredisTheorem.smoothDivisorChoices.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


