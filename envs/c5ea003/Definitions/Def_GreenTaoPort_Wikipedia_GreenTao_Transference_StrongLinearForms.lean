-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:51:20.735476+00:00
-- url     : https://prove2.me/theorems/bd016c7d-f1b2-40dd-9a62-2ba35934557a
-- title:
--   Boolean subproducts and centered finite-product expansions
-- statement:
--   A Boolean cube on a finite index type is the set of Boolean selectors. For a real vector $(a_i)$, the bundle defines its centered product $\prod_i(a_i-1)$, the subproduct selected by a Boolean exponent, and the corresponding inclusion–exclusion sign, with one minus sign for each unselected coordinate.
--
--   For a finite family of real functions, the Boolean-subproduct condition requires every selected subproduct to have normalized mean within $\eta$ of one. The empty selection is included. These finite algebraic definitions isolate the centered-product expansions used by the strong linear-forms argument.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/StrongLinearForms.lean#L30-L233

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Chebyshev
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Algebraic strong-linear-forms primitives

This file contains the finite algebra behind the strong linear-forms and
densification arguments:

* centered factors `ν - 1`;
* products over Boolean cubes and corner systems;
* exact Boolean inclusion--exclusion expansions;
* cancellation of the constant terms;
* the resulting centered CFZ-moment estimate from the ordinary
  linear-forms condition;
* an `L²` contraction for coordinate-sum fiber convolutions, and a
  hypothesis-driven centered-moment consequence.

No analytic estimate for a sieve majorant is asserted here. Those estimates
must supply the explicit subproduct or moment hypotheses used below.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The Boolean cube with coordinate set `ι`. -/
abbrev BooleanCube (ι : Type*) :=
  ι → Bool





/-- Product of the centered entries of a finite vector. -/
def centeredProduct {ι : Type*} [Fintype ι] (a : ι → ℝ) : ℝ :=
  ∏ i, (a i - 1)

/-- The subproduct selected by a Boolean exponent vector. -/
def cubeSelectedProduct {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (e : BooleanCube ι) : ℝ :=
  ∏ i, if e i then a i else 1

/-- The sign contributed by the unselected entries in a Boolean
inclusion--exclusion expansion. -/
def cubeSign {ι : Type*} [Fintype ι] (e : BooleanCube ι) : ℝ :=
  ∏ i, if e i then 1 else -1

/-- A raw term in the expansion of `∏ i, (a i - 1)`. -/
def cubeExpansionTerm {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (e : BooleanCube ι) : ℝ :=
  ∏ i, if e i then a i else -1































/-- Every Boolean-selected subproduct has mean within `η` of one. -/
def HasBooleanSubproductCondition
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (a : ι → Ω → ℝ) (η : ℝ) : Prop :=
  ∀ e : BooleanCube ι,
    |mean (fun x =>
      cubeSelectedProduct (fun i => a i x) e) - 1| ≤ η





/-! ## Specialization to the CFZ linear-forms system -/



















/-! ## Fiber convolution and second moments -/















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.centeredProduct.eq_1,
    `Wikipedia.SzemeredisTheorem.cubeExpansionTerm.eq_1,
    `Wikipedia.SzemeredisTheorem.cubeSelectedProduct.eq_1,
    `Wikipedia.SzemeredisTheorem.cubeSign.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


