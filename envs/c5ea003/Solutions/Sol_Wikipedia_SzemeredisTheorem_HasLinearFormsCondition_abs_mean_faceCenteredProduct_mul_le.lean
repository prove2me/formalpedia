-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HasLinearFormsCondition.abs_mean_faceCenteredProduct_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:55:45.290764+00:00
-- url     : https://prove2.me/submissions/1efcbb28-fdfa-4433-a7b3-5d3d1a7e7230

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_faceCenteredProduct_mul_linearFormsProduct_eq_sum

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









/-! ## Specialization to the CFZ linear-forms system -/



















/-! ## Fiber convolution and second moments -/















end Wikipedia.SzemeredisTheorem

end
/-!
# Weighted endpoint of the strong linear-forms argument

The CFZ densification proof applies Cauchy--Schwarz repeatedly to a
centered factor on one simplex face.  At the final doubled stage, every
remaining relatively bounded factor has been replaced by either its
majorant or by one.  The resulting expression is

* the product of all centered copies of the selected face; times
* an arbitrary Boolean-selected subproduct of the other CFZ forms.

This file proves the exact quantitative linear-forms estimate for that
endpoint.  The still-missing recursive Cauchy--Schwarz bridge belongs in
the same module after this algebraic target.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

/-- Quantitative weighted strong-linear-forms endpoint.

An arbitrary fixed subproduct of all other CFZ faces may accompany the
centered cube on `j`; the same `2^(2^(k-1))` inclusion--exclusion loss as
for the unweighted centered face suffices. -/
theorem solution
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (hLF : HasLinearFormsCondition k N ν η)
    (j : Fin k)
    (other : LinearFormsExponent k)
    (hother : ∀ ω, other j ω = false) :
    |mean (fun x =>
        faceCenteredProduct k N ν j x *
          linearFormsProduct k N ν other x)| ≤
      (2 : ℝ) ^ Fintype.card (DeletedCube k j) * η := by
  rw [mean_faceCenteredProduct_mul_linearFormsProduct_eq_sum
    ν j other hother]
  have hsign :
      ∑ face : BooleanCube (DeletedCube k j),
        cubeSign face = 0 :=
    sum_cubeSign_eq_zero
  rw [sum_mul_eq_sum_mul_sub_one_of_sum_eq_zero
    (fun face : BooleanCube (DeletedCube k j) =>
      cubeSign face)
    (fun face =>
      mean (linearFormsProduct k N ν
        (overwriteFaceExponent j face other)))
    hsign]
  calc
    |∑ face : BooleanCube (DeletedCube k j),
        cubeSign face *
          (mean (linearFormsProduct k N ν
            (overwriteFaceExponent j face other)) - 1)| ≤
        ∑ face : BooleanCube (DeletedCube k j),
          |cubeSign face *
            (mean (linearFormsProduct k N ν
              (overwriteFaceExponent j face other)) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ _face : BooleanCube (DeletedCube k j), η := by
      apply Finset.sum_le_sum
      intro face _hface
      simpa [abs_mul] using
        hLF (overwriteFaceExponent j face other)
    _ =
        (2 : ℝ) ^ Fintype.card (DeletedCube k j) * η := by
      simp [BooleanCube, Fintype.card_bool]
