-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:06:36.535968+00:00
-- url     : https://prove2.me/theorems/896b7aa3-d795-4ffe-b554-b97276158f0a
-- title:
--   Quotient blocks and carry boundaries for cyclic CFZ forms
-- statement:
--   For natural vectors, $\operatorname{SameQuotientBlock}(D,x,y)$ means that $x_i/D=y_i/D$ in every coordinate. The bundle defines finite affine strips inside a natural box, the lower corner $D\lfloor x/D\rfloor$ of a block, and uniform CFZ carry and block-variation bounds. For a nonzero modulus $N$, a point is carry-bad for a form if another point of the same side-$D$ quotient block inside the standard box has a different canonical carry. Finite bad sets and their union over a selected form family are also provided.
--
--   The hyperplane envelope is the union of affine strips around the multiples $Nc$ for a bounded carry range. A fixed carry $c$ changes only the constant term of the W-tricked affine form, by $-WNc$. A final construction pulls a finite bad set of natural vectors back to the corresponding typed finite box.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCarryBlockBoundary.lean#L26-L1065

import Mathlib.Data.Int.Interval
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
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

/-- Two natural vectors lie in the same coordinatewise quotient block of
side `D`. -/
def SameQuotientBlock {ι : Type*} (D : ℕ)
    (x y : ι → ℕ) : Prop :=
  ∀ i, x i / D = y i / D

















/-! ## A generic unit-coefficient strip count -/

/-- Integer points in the standard box lying in a closed affine strip. -/
def affineStripInBox {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (N L : ℕ) (ψ : AffineForm ι ℤ) (a : ℤ) :
    Finset (ι → ℕ) :=
  (natBox (fun _ : ι => N)).filter fun x =>
    Int.natAbs
      (ψ.eval (fun i => (x i : ℤ)) - a) ≤ L







/-! ## CFZ coefficient and block-diameter facts -/





/-! ## Carry-change hyperplanes -/

/-- The uniform carry range on the standard CFZ box. -/
def cfzCarryRange (k : ℕ) : ℕ :=
  Fintype.card (CFZVariable k) * k + 1

/-- The maximum affine variation of one CFZ form inside a side-`D`
quotient block. -/
def cfzBlockVariation (k D : ℕ) : ℕ :=
  Fintype.card (CFZVariable k) * k * D









/-- A point is bad for one CFZ form when another point of its quotient
block has a different canonical carry. -/
def CFZCarryBadPoint
    {k N : ℕ} [NeZero N]
    (D : ℕ) (q : CFZFormIndex k)
    (x : CFZVariable k → ℕ) : Prop :=
  x ∈ natBox (fun _ : CFZVariable k => N) ∧
    ∃ y ∈ natBox (fun _ : CFZVariable k => N),
      SameQuotientBlock D x y ∧
        cfzCarry (N := N) q x ≠
          cfzCarry (N := N) q y

/-- The finite set of bad points for one CFZ form. -/
noncomputable def cfzCarryBadPoints
    {k N : ℕ} [NeZero N]
    (D : ℕ) (q : CFZFormIndex k) :
    Finset (CFZVariable k → ℕ) := by
  classical
  exact
    (natBox (fun _ : CFZVariable k => N)).filter
      (CFZCarryBadPoint (N := N) D q)









/-! ## Explicit bad-point counts -/

/-- Union of the finitely many strips that can contain a bad point for one
CFZ form. -/
noncomputable def cfzCarryHyperplaneEnvelope
    {k N : ℕ} (D : ℕ) (q : CFZFormIndex k) :
    Finset (CFZVariable k → ℕ) := by
  classical
  exact
    (Finset.Icc (-(cfzCarryRange k : ℤ))
        (cfzCarryRange k : ℤ)).biUnion fun c =>
      affineStripInBox N (cfzBlockVariation k D)
        (cfzAffineForm q) ((N : ℤ) * c)









/-- Bad points for at least one form of a finite selected family. -/
noncomputable def cfzFamilyCarryBadPoints
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (D : ℕ) (forms : κ → CFZFormIndex k) :
    Finset (CFZVariable k → ℕ) := by
  classical
  exact Finset.univ.biUnion fun q =>
    cfzCarryBadPoints (N := N) D (forms q)





/-! ## Carry-adjusted affine block model -/

/-- The lower corner of the coordinatewise quotient block containing `x`. -/
def quotientBlockBase {ι : Type*} (D : ℕ)
    (x : ι → ℕ) : ι → ℕ :=
  fun i => D * (x i / D)







/-- The integer W-tricked affine form with the correction
`-W*N*c` corresponding to a fixed carry `c`. -/
def cfzCarryAdjustedAffineForm
    {k : ℕ} (N W b : ℕ)
    (q : CFZFormIndex k) (c : ℤ) :
    AffineForm (CFZVariable k) ℤ where
  constant :=
    (wTrickedAffineForm W b (cfzAffineForm q)).constant -
      (W : ℤ) * (N : ℤ) * c
  coefficient :=
    (wTrickedAffineForm W b (cfzAffineForm q)).coefficient





















/-! ## A normalized disagreement bound -/

/-- Pull a natural-vector bad set back to the typed finite box. -/
noncomputable def finiteBoxBadSet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) (bad : Finset (ι → ℕ)) :
    Finset (FiniteBox side) := by
  classical
  exact Finset.univ.filter fun x =>
    (fun i => (x i : ℕ)) ∈ bad



















/-! ## Carry-dependent affine residue model -/















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.affineStripInBox.eq_1,
    `Wikipedia.SzemeredisTheorem.cfzBlockVariation.eq_1,
    `Wikipedia.SzemeredisTheorem.cfzCarryAdjustedAffineForm.eq_1,
    `Wikipedia.SzemeredisTheorem.cfzCarryBadPoints.congr_simp,
    `Wikipedia.SzemeredisTheorem.cfzCarryRange.eq_1,
    `Wikipedia.SzemeredisTheorem.cfzFamilyCarryBadPoints.congr_simp,
    `Wikipedia.SzemeredisTheorem.finiteBoxBadSet.eq_1,
    `Wikipedia.SzemeredisTheorem.quotientBlockBase.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


