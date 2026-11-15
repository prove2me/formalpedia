-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_mean_centeredProduct_le_card_mul
-- name    : Wikipedia.SzemeredisTheorem.abs_mean_centeredProduct_le_card_mul
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:40:39.056268+00:00
-- url     : https://prove2.me/theorems/e8949b8a-02d4-4469-9934-ffd7b452f55e
-- title:
--   A centered-product bound from Boolean subproduct control
-- statement:
--   Let $\Omega$ be finite and let $\iota$ be a finite nonempty type with decidable equality. If a family $a_i:\Omega\to\mathbb R$ satisfies the Boolean subproduct condition with error $\eta$, then the absolute mean of its centered product is at most $|\mathrm{BooleanCube}(\iota)|\eta$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/StrongLinearForms.lean#L235-L258

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Chebyshev
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.abs_mean_centeredProduct_le_card_mul
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [Nonempty ι]
    {a : ι → Ω → ℝ} {η : ℝ}
    (h : HasBooleanSubproductCondition a η) :
    |mean (fun x => centeredProduct (fun i => a i x))| ≤
      (Fintype.card (BooleanCube ι) : ℝ) * η := by sorry
