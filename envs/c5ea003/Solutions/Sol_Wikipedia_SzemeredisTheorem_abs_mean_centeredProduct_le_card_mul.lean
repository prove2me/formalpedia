-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_mean_centeredProduct_le_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:18:05.890255+00:00
-- url     : https://prove2.me/submissions/9f29eb17-a432-465e-9490-c402c7441eec

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_centeredProduct_eq_sum

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



















@[simp]
theorem abs_cubeSign {ι : Type*} [Fintype ι]
    (e : BooleanCube ι) :
    |cubeSign e| = 1 := by
  rw [cubeSign, Finset.abs_prod]
  apply Finset.prod_eq_one
  intro i _
  cases e i <;> simp

/-- The signs in a nonempty Boolean cube cancel. -/
theorem sum_cubeSign_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ∑ e : BooleanCube ι, cubeSign e = 0 := by
  have h := (Fintype.prod_sum
    (fun _ : ι => fun b : Bool => if b then (1 : ℝ) else -1)).symm
  simpa [cubeSign] using h



















/-- If the coefficients sum to zero, one may center every summand without
changing the weighted sum. -/
theorem sum_mul_eq_sum_mul_sub_one_of_sum_eq_zero
    {κ : Type*} [Fintype κ] (s m : κ → ℝ)
    (hs : ∑ e, s e = 0) :
    (∑ e, s e * m e) =
      ∑ e, s e * (m e - 1) := by
  calc
    (∑ e, s e * m e) =
        ∑ e, (s e * (m e - 1) + s e) := by
      apply Fintype.sum_congr
      intro e
      ring
    _ = (∑ e, s e * (m e - 1)) + ∑ e, s e :=
      Finset.sum_add_distrib
    _ = _ := by rw [hs, add_zero]

/-- Cancellation of all constant terms in the average of a nonempty
centered product. -/
theorem mean_centeredProduct_eq_sum_deviations
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [Nonempty ι]
    (a : ι → Ω → ℝ) :
    mean (fun x => centeredProduct (fun i => a i x)) =
      ∑ e : BooleanCube ι, cubeSign e *
        (mean (fun x =>
          cubeSelectedProduct (fun i => a i x) e) - 1) := by
  rw [mean_centeredProduct_eq_sum]
  exact sum_mul_eq_sum_mul_sub_one_of_sum_eq_zero _ _
    sum_cubeSign_eq_zero







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
/-- Inclusion--exclusion bounds a centered product by the number of Boolean
subproducts times the common error. -/
theorem solution
    {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [Nonempty ι]
    {a : ι → Ω → ℝ} {η : ℝ}
    (h : HasBooleanSubproductCondition a η) :
    |mean (fun x => centeredProduct (fun i => a i x))| ≤
      (Fintype.card (BooleanCube ι) : ℝ) * η := by
  rw [mean_centeredProduct_eq_sum_deviations]
  calc
    |∑ e : BooleanCube ι, cubeSign e *
        (mean (fun x =>
          cubeSelectedProduct (fun i => a i x) e) - 1)| ≤
        ∑ e : BooleanCube ι, |cubeSign e *
          (mean (fun x =>
            cubeSelectedProduct (fun i => a i x) e) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e : BooleanCube ι, η := by
      apply Finset.sum_le_sum
      intro e _
      simpa [abs_mul] using h e
    _ = (Fintype.card (BooleanCube ι) : ℝ) * η := by
      simp
