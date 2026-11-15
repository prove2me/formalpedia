-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:08:06.147456+00:00
-- url     : https://prove2.me/theorems/4ec5f077-3247-432f-b715-4c415f320e36
-- title:
--   The canonical finite partition by complete CFZ carry vectors
-- statement:
--   A finite family of CFZ form indices assigns to each natural doubled-variable point its vector of integer carries when the form values are reduced modulo a positive modulus $N$.
--
--   The admissible carry-vector set is the finite Cartesian product of the integer interval $[-C_k,C_k]$, where $C_k$ is the uniform carry bound for progression length $k$. It depends only on that length and the family index type. The cell for a specified carry vector is its exact fiber inside the standard coordinate box $\{0,\ldots,N-1\}^{V}$. The partition is fixed before choosing divisor families or affine residue constants.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalCarryCellPartition.lean#L29-L89

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Lean
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
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


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

/-- The complete canonical carry vector of a finite selected CFZ family at
one natural point. -/
def cfzCanonicalCarryVector
    {κ : Type*} {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (x : CFZVariable k → ℕ) : κ → ℤ :=
  fun q => cfzCarry (N := N) (forms q) x

/-- All carry vectors in the uniform coordinatewise range.  The finset
depends only on `k` and the finite index type, not on `N`, the divisor
choice, or the affine constants. -/
noncomputable def cfzCanonicalCarryVectorChoices
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (k : ℕ) : Finset (κ → ℤ) :=
  Fintype.piFinset fun _q : κ =>
    Finset.Icc (-(cfzCarryRange k : ℤ))
      (cfzCarryRange k : ℤ)





/-! ## The canonical cells -/

/-- The fiber of one complete carry vector inside the standard natural
box. -/
def cfzCanonicalCarryCell
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) :
    Finset (CFZVariable k → ℕ) :=
  (natBox (fun _ : CFZVariable k => N)).filter
    fun x => cfzCanonicalCarryVector (N := N) forms x = carry









/-! ## Exact partition identities -/







end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cfzCanonicalCarryCell.eq_1,
    `Wikipedia.SzemeredisTheorem.cfzCanonicalCarryVector.congr_simp
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


