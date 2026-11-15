-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:09:39.010123+00:00
-- url     : https://prove2.me/theorems/59b14436-be78-4253-a6b9-49c77ec32440
-- title:
--   Canonical carry indicators and quotient-block approximations
-- statement:
--   For a finite selected family of CFZ forms, a positive modulus $N$, and an integer carry vector $c$, the canonical indicator is one exactly at natural points whose complete carry vector equals $c$, and zero elsewhere.
--
--   Its side-$D$ block approximation samples this indicator at the lower corner of the quotient block containing the point. The trimmed bad-point set restricts the previously defined family carry-transition bad set to the coordinate box with side length trimmed down to a multiple of $D$. These objects compare exact carry cells with blockwise constant approximations without introducing a divisor-dependent partition.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalCarryCellDiscrepancy.lean#L31-L129

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
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


/-!
# Residue discrepancy on canonical CFZ carry cells

The canonical carry partition freezes the affine family independently of
all divisor choices.  To use it in the divisor expansion, one must still
average a periodic residue function on each carry fiber.

This file starts that comparison at the exact level.  A block indicator
tests the carry vector at the lower corner of a side-`D` quotient block.
On the coordinatewise box trimmed to a multiple of `D`, that indicator
depends only on the quotient coordinate.  It is therefore independent of
every `D`-periodic residue function, and their normalized mean factors
exactly.

The next lemmas compare this block indicator with the genuine canonical
cell indicator.  They can disagree only on the already-counted family
carry-bad set.  Together with the outer trimming boundary this yields the
required `O_{k,m}(D/N)` discrepancy without introducing a new geometric
axiom.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Point and quotient-block indicators -/

/-- Real indicator that a point has the prescribed complete canonical carry
vector. -/
noncomputable def cfzCanonicalCarryIndicator
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (x : CFZVariable k → ℕ) : ℝ :=
  if cfzCanonicalCarryVector (N := N) forms x = carry then 1 else 0

/-- Blockwise approximation to the canonical carry indicator: sample the
carry vector at the lower corner of the side-`D` quotient block. -/
noncomputable def cfzCanonicalCarryBlockIndicator
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D : ℕ)
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (x : CFZVariable k → ℕ) : ℝ :=
  cfzCanonicalCarryIndicator (N := N) forms carry
    (quotientBlockBase D x)









/-! ## The carry-bad set inside the complete-block box -/

/-- Restrict the global family carry-bad set to the box trimmed to complete
side-`D` quotient blocks. -/
noncomputable def cfzTrimmedFamilyCarryBadPoints
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D : ℕ) (forms : κ → CFZFormIndex k) :
    Finset (CFZVariable k → ℕ) :=
  (cfzFamilyCarryBadPoints (N := N) D forms).filter fun x =>
    x ∈ natBox
      (fun _ : CFZVariable k => trimToMultiple D N)







/-! ## Exact quotient/residue factorization -/





/-! ## Point/block comparison on the trimmed box -/





/-! ## Canonical-cell residue discrepancy on the trimmed box -/



/-! ## Full-box discrepancy -/



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cfzCanonicalCarryBlockIndicator.congr_simp,
    `Wikipedia.SzemeredisTheorem.cfzCanonicalCarryIndicator.congr_simp,
    `Wikipedia.SzemeredisTheorem.cfzTrimmedFamilyCarryBadPoints.congr_simp,
    `Wikipedia.SzemeredisTheorem.cfzTrimmedFamilyCarryBadPoints.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


