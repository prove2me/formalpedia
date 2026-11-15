-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.faceCenteredProduct_mul_linearFormsProduct_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:28:17.684505+00:00
-- url     : https://prove2.me/submissions/5137a88b-b789-4cee-9515-bb1883bf078d

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_faceSelectedProduct_mul_linearFormsProduct_eq_overwrite

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

open Wikipedia.SzemeredisTheorem in
/-- Pointwise expansion of the weighted centered-face endpoint into
ordinary CFZ subproducts. -/
theorem solution
    {k N : ℕ}
    (ν : ZMod N → ℝ) (j : Fin k)
    (other : LinearFormsExponent k)
    (hother : ∀ ω, other j ω = false)
    (x : CubePoint k N) :
    faceCenteredProduct k N ν j x *
        linearFormsProduct k N ν other x =
      ∑ face : BooleanCube (DeletedCube k j),
        cubeSign face *
          linearFormsProduct k N ν
            (overwriteFaceExponent j face other) x := by
  rw [faceCenteredProduct]
  change
    centeredProduct
          (fun ω : DeletedCube k j =>
            faceFactorFamily k N ν j ω x) *
        linearFormsProduct k N ν other x =
      _
  rw [centeredProduct_eq_sum_sign_mul_selected,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro face _hface
  rw [mul_assoc]
  apply congrArg (fun z : ℝ => cubeSign face * z)
  exact
    faceSelectedProduct_mul_linearFormsProduct_eq_overwrite
      ν j face other hother x
