-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_centeredProduct_eq_sum
-- name    : Wikipedia.SzemeredisTheorem.mean_centeredProduct_eq_sum
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:29.026993+00:00
-- url     : https://prove2.me/theorems/db5b59ee-6d2f-4ded-b87b-e616ce4ffe91
-- title:
--   Averaged inclusion–exclusion for centered products
-- statement:
--   Let $\Omega$ and $I$ be finite sets, and let $a_i:\Omega\to\mathbb R$ for $i\in I$. Then
--   $$
--   \mathbb E_{x\in\Omega}\prod_{i\in I}(a_i(x)-1)
--   =\sum_{S\subseteq I}(-1)^{\lvert I\setminus S\rvert}\mathbb E_{x\in\Omega}\prod_{i\in S}a_i(x).
--   $$
--   The source indexes subsets by their Boolean indicator vectors. This is the exact centered-product expansion averaged term by term; no bounds or sign conditions on the functions are assumed.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/StrongLinearForms.lean#L169-L194

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

theorem Wikipedia.SzemeredisTheorem.mean_centeredProduct_eq_sum
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (a : ι → Ω → ℝ) :
    mean (fun x => centeredProduct (fun i => a i x)) =
      ∑ e : BooleanCube ι,
        cubeSign e *
          mean (fun x =>
            cubeSelectedProduct (fun i => a i x) e) := by sorry
