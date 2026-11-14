-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:49:41.537094+00:00
-- url     : https://prove2.me/theorems/e0b5023a-c2f7-44b1-af87-08a28508c02f
-- title:
--   Affine forms and the CFZ linear-forms condition
-- statement:
--   An affine form consists of a constant and a coefficient function; on a finite variable set it evaluates as the constant plus the sum of coefficient–variable products. For the arithmetic-progression system, a doubled variable vector has coordinates $x_i^0,x_i^1$ in $\mathbb Z/N\mathbb Z$. A deleted Boolean cube vertex $\omega$ chooses one value at each coordinate other than $j$, giving the form
--
--   $$
--   \psi_{j,\omega}(x)=\sum_{i\ne j}(i-j)x_i^{\omega_i}.
--   $$
--
--   The integer coefficient $i-j$ is reduced modulo $N$. A Boolean exponent selects any subfamily of these forms, and its product is the product of a real majorant $\nu$ evaluated at precisely the selected forms. For $N>0$, the quantitative linear-forms condition requires the normalized average of every such product to differ from one by at most the real tolerance $\eta$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/LinearForms/Basic.lean#L23-L79

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Data.ZMod.Basic
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Affine forms and the arithmetic-progression linear-forms system

The relative Szemerédi theorem uses one specific family of linear forms.  For
`j < k` and a vertex `ω` of the cube with the `j`th coordinate deleted, the
form is

`ψ_{j,ω}(x) = ∑ i ≠ j, (i - j) * xᵢ^(ωᵢ)`.

The quantitative predicate at the end of this file says that every
subproduct of these `k * 2^(k-1)` forms has normalized average within `η` of
one.  Encoding subproducts by Boolean exponents exactly matches the
Conlon--Fox--Zhao linear-forms condition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A finitely supported affine form, represented by all of its coefficients
on a finite index type. -/
structure AffineForm (ι R : Type*) [Zero R] where
  constant : R
  coefficient : ι → R

namespace AffineForm

/-- Evaluate an affine form at a vector. -/
def eval {ι R : Type*} [Fintype ι] [Semiring R]
    (ψ : AffineForm ι R) (x : ι → R) : R :=
  ψ.constant + ∑ i, ψ.coefficient i * x i



end AffineForm

/-- A point carrying two independent values in every one of `k`
coordinates. -/
abbrev CubePoint (k N : ℕ) :=
  Fin k → Bool → ZMod N

/-- A Boolean vertex of the `(k-1)`-cube obtained by deleting coordinate
`j`. -/
abbrev DeletedCube (k : ℕ) (j : Fin k) :=
  {i : Fin k // i ≠ j} → Bool

/-- The Conlon--Fox--Zhao form indexed by `j` and `ω`. -/
def apLinearForm (k N : ℕ) (j : Fin k) (ω : DeletedCube k j)
    (x : CubePoint k N) : ZMod N :=
  ∑ i : {i : Fin k // i ≠ j},
    (((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i.1 (ω i)

/-- Boolean choices of the subproduct of the arithmetic-progression linear-forms
system to be tested. -/
abbrev LinearFormsExponent (k : ℕ) :=
  (j : Fin k) → DeletedCube k j → Bool

/-- The subproduct selected by `e`, evaluated at the doubled variable
vector `x`. -/
def linearFormsProduct (k N : ℕ) (ν : ZMod N → ℝ)
    (e : LinearFormsExponent k) (x : CubePoint k N) : ℝ :=
  ∏ j : Fin k, ∏ ω : DeletedCube k j,
    if e j ω then ν (apLinearForm k N j ω x) else 1

/-- Quantitative `k`-linear-forms condition.

Every subproduct of the canonical arithmetic-progression forms must have
normalized average within `η` of one. -/
def HasLinearFormsCondition (k N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ) (η : ℝ) : Prop :=
  ∀ e : LinearFormsExponent k,
    |mean (linearFormsProduct k N ν e) - 1| ≤ η



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.AffineForm.ctorIdx,
    `Wikipedia.SzemeredisTheorem.AffineForm.eval.eq_1,
    `Wikipedia.SzemeredisTheorem.AffineForm.mk.inj,
    `Wikipedia.SzemeredisTheorem.AffineForm.mk.injEq,
    `Wikipedia.SzemeredisTheorem.AffineForm.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.AffineForm.noConfusionType
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


