-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:48.652675+00:00
-- url     : https://prove2.me/theorems/86f79e95-49a8-4829-bb86-d49feeac4278
-- title:
--   Normalized fiber convolutions over coordinate-sum fibers
-- statement:
--   For a tuple of positive arity in an additive commutative group, prescribing its sum $z$ and its tail uniquely determines its head. This gives the explicit equivalence between tuples and pairs consisting of their sum and tail.
--
--   On a finite group, fiber convolution averages an arbitrary tuple weight over this parametrized sum fiber. At arity zero it uses the density $|G|\,1_{\{0\}}(z)$ times the unique empty-tuple weight, preserving the normalized disintegration convention. The product of deleted-coordinate tests defines a tuple weight; its fiber convolution is the generalized convolution attached to that test family.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/GeneralizedConvolution.lean#L18-L168

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Generalized convolutions on finite additive groups

For positive arity, the generalized convolution is the normalized average of
a weight over a fiber of the coordinate-sum map. At arity zero the sum map
has only the value zero, so the fiber density is a scaled delta function.
Keeping this scaling makes the pairing identity valid without an arity
exception; the `[0,1]` range statement is correctly restricted to positive
arity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The tuple with prescribed coordinate sum `z` and prescribed tail `y`.
The zeroth coordinate is the unique value making the total sum equal `z`. -/
def sumFiberTuple {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) : Fin (n + 1) → G :=
  Fin.cons (z - ∑ i, y i) y





@[simp]
theorem sum_sumFiberTuple {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) :
    ∑ i, sumFiberTuple n z y i = z := by
  simp [sumFiberTuple, Fin.sum_univ_succ]

/-- Splitting a nonempty tuple into its coordinate sum and its tail is an
equivalence. -/
def sumFiberEquiv (G : Type*) [AddCommGroup G] (n : ℕ) :
    (Fin (n + 1) → G) ≃ G × (Fin n → G) where
  toFun x := (∑ i, x i, Fin.tail x)
  invFun p := sumFiberTuple n p.1 p.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (∑ k, x k) - ∑ j, Fin.tail x j = x 0
      rw [Fin.sum_univ_succ]
      change x 0 + (∑ j : Fin n, x j.succ) -
        ∑ j : Fin n, x j.succ = x 0
      abel
    · rfl
  right_inv p := by
    apply Prod.ext
    · exact sum_sumFiberTuple n p.1 p.2
    · funext j
      rfl

/-- The density, relative to uniform measure on `G`, of the only nonempty
fiber of the zero-coordinate sum map. It equals `|G|` at zero and vanishes
elsewhere. -/
noncomputable def zeroFiberDelta
    {G : Type*} [Fintype G] [AddCommGroup G] (z : G) : ℝ := by
  classical
  exact if z = 0 then (Fintype.card G : ℝ) else 0







/-- The normalized fiber convolution of an arbitrary tuple weight.

For `r = n + 1`, this is the average of `w` on the fiber with sum `z`,
parametrized by `sumFiberTuple`. For `r = 0`, the scaled delta convention
preserves the exact disintegration identity. -/
noncomputable def fiberConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w : (Fin r → G) → ℝ) (z : G) : ℝ := by
  cases r with
  | zero =>
      exact zeroFiberDelta z * w (fun i => Fin.elim0 i)
  | succ n =>
      exact mean fun y : Fin n → G => w (sumFiberTuple n z y)





/-- The product weight associated to a family of deleted-coordinate tests. -/
def cutTestProduct {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) (x : Fin r → G) : ℝ :=
  ∏ i, u i (eraseCoordinate i x)











/-- The generalized convolution attached to a family of cut tests. -/
noncomputable def generalizedConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (u : CutTestFamily G r) (z : G) : ℝ :=
  fiberConvolution r (cutTestProduct u) z















































end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cutTestProduct.eq_1,
    `Wikipedia.SzemeredisTheorem.generalizedConvolution.eq_1,
    `Wikipedia.SzemeredisTheorem.sumFiberTuple.eq_1,
    `Wikipedia.SzemeredisTheorem.zeroFiberDelta.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


