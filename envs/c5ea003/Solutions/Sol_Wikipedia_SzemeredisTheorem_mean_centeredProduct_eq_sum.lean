-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_centeredProduct_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:31.746357+00:00
-- url     : https://prove2.me/submissions/9b5bbcab-4c62-432c-a983-85d0be11a06f

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

section






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























/-- Split a raw expansion term into its sign and selected subproduct. -/
theorem cubeExpansionTerm_eq_sign_mul_selected
    {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (e : BooleanCube ι) :
    cubeExpansionTerm a e =
      cubeSign e * cubeSelectedProduct a e := by
  rw [cubeExpansionTerm, cubeSign, cubeSelectedProduct,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases e i <;> simp

/-- Exact Boolean expansion of a product of centered factors. -/
theorem centeredProduct_eq_sum_cube
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) :
    centeredProduct a =
      ∑ e : BooleanCube ι, cubeExpansionTerm a e := by
  rw [centeredProduct]
  calc
    (∏ i, (a i - 1)) =
        ∏ i, ∑ b : Bool, if b then a i else -1 := by
      apply Fintype.prod_congr
      intro i
      simp
      ring
    _ = _ := Fintype.prod_sum _

/-- Inclusion--exclusion form of the centered-product expansion. -/
theorem centeredProduct_eq_sum_sign_mul_selected
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) :
    centeredProduct a =
      ∑ e : BooleanCube ι,
        cubeSign e * cubeSelectedProduct a e := by
  rw [centeredProduct_eq_sum_cube]
  apply Fintype.sum_congr
  intro e
  exact cubeExpansionTerm_eq_sign_mul_selected a e









/-- Normalized averaging commutes with a finite sum. -/
theorem mean_fintype_sum
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (F : ι → Ω → ℝ) :
    mean (fun x => ∑ i, F i x) = ∑ i, mean (F i) := by
  unfold mean
  exact Finset.expect_sum_comm Finset.univ Finset.univ
    (fun x i => F i x)













/-! ## Specialization to the CFZ linear-forms system -/



















/-! ## Fiber convolution and second moments -/















end Wikipedia.SzemeredisTheorem

end
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

open Wikipedia.SzemeredisTheorem in
/-- Average the exact centered-product expansion term by term. -/
theorem solution
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (a : ι → Ω → ℝ) :
    mean (fun x => centeredProduct (fun i => a i x)) =
      ∑ e : BooleanCube ι,
        cubeSign e *
          mean (fun x =>
            cubeSelectedProduct (fun i => a i x) e) := by
  calc
    mean (fun x => centeredProduct (fun i => a i x)) =
        mean (fun x => ∑ e : BooleanCube ι,
          cubeSign e *
            cubeSelectedProduct (fun i => a i x) e) := by
      apply congrArg mean
      funext x
      exact centeredProduct_eq_sum_sign_mul_selected
        (fun i => a i x)
    _ = ∑ e : BooleanCube ι,
        mean (fun x => cubeSign e *
          cubeSelectedProduct (fun i => a i x) e) :=
      mean_fintype_sum _
    _ = _ := by
      apply Fintype.sum_congr
      intro e
      exact mean_smul (cubeSign e) _
