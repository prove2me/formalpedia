-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_faceCenteredProduct_mul_linearFormsProduct_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:54:41.026352+00:00
-- url     : https://prove2.me/submissions/a9c01f1b-7c56-4926-b26d-98ff0722b0dc

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_faceCenteredProduct_mul_linearFormsProduct_eq_sum

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
/-- Averaged form of the exact endpoint expansion. -/
theorem solution
    {k N : ℕ} [NeZero N]
    (ν : ZMod N → ℝ) (j : Fin k)
    (other : LinearFormsExponent k)
    (hother : ∀ ω, other j ω = false) :
    mean (fun x =>
        faceCenteredProduct k N ν j x *
          linearFormsProduct k N ν other x) =
      ∑ face : BooleanCube (DeletedCube k j),
        cubeSign face *
          mean (linearFormsProduct k N ν
            (overwriteFaceExponent j face other)) := by
  calc
    mean (fun x =>
        faceCenteredProduct k N ν j x *
          linearFormsProduct k N ν other x) =
        mean (fun x =>
          ∑ face : BooleanCube (DeletedCube k j),
            cubeSign face *
              linearFormsProduct k N ν
                (overwriteFaceExponent j face other) x) := by
      apply congrArg mean
      funext x
      exact
        faceCenteredProduct_mul_linearFormsProduct_eq_sum
          ν j other hother x
    _ =
        ∑ face : BooleanCube (DeletedCube k j),
          mean (fun x =>
            cubeSign face *
              linearFormsProduct k N ν
                (overwriteFaceExponent j face other) x) :=
      mean_fintype_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro face _hface
      exact mean_smul (cubeSign face) _
