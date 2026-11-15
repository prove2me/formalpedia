-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HasLinearFormsCondition.hasFaceBooleanSubproductCondition
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:15:39.089212+00:00
-- url     : https://prove2.me/submissions/c78f8adb-d2c2-4760-a616-5dc959f17f7b

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# Centered moments on one progression face

The CFZ linear-forms condition controls every Boolean subproduct of the
forms belonging to a fixed deleted coordinate.  Inclusion--exclusion then
bounds the product of all centered factors on that face.  This is the
linear-forms estimate that appears at the endpoint of the generalized
von Neumann Cauchy--Schwarz argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators











/-- Selecting a subproduct of one face agrees with selecting the
corresponding subproduct of the full CFZ system. -/
theorem faceSelectedProduct_eq_linearFormsProduct
    (k N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin k) (e : BooleanCube (DeletedCube k j))
    (x : CubePoint k N) :
    cubeSelectedProduct
        (fun ω => faceFactorFamily k N ν j ω x) e =
      linearFormsProduct k N ν
        (faceLinearFormsExponent j e) x := by
  rw [linearFormsProduct, Fintype.prod_eq_single j]
  · simp [cubeSelectedProduct, faceFactorFamily,
      faceLinearFormsExponent]
  · intro j' hj'
    apply Fintype.prod_eq_one
    intro ω
    simp [faceLinearFormsExponent, hj']





























end Wikipedia.SzemeredisTheorem

end
/-!
# Centered moments on one progression face

The CFZ linear-forms condition controls every Boolean subproduct of the
forms belonging to a fixed deleted coordinate.  Inclusion--exclusion then
bounds the product of all centered factors on that face.  This is the
linear-forms estimate that appears at the endpoint of the generalized
von Neumann Cauchy--Schwarz argument.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

/-- The full linear-forms condition restricts to the Boolean subproduct
condition on any one face. -/
theorem solution
    {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition k N ν η)
    (j : Fin k) :
    HasBooleanSubproductCondition
      (faceFactorFamily k N ν j) η := by
  intro e
  have hfun :
      (fun x => cubeSelectedProduct
        (fun ω => faceFactorFamily k N ν j ω x) e) =
      linearFormsProduct k N ν
        (faceLinearFormsExponent j e) := by
    funext x
    exact faceSelectedProduct_eq_linearFormsProduct
      k N ν j e x
  rw [hfun]
  exact h (faceLinearFormsExponent j e)
