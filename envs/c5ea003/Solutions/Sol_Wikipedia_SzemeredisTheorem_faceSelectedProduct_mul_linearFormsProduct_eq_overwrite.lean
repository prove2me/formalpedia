-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.faceSelectedProduct_mul_linearFormsProduct_eq_overwrite
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:25:03.84408+00:00
-- url     : https://prove2.me/submissions/fb2ff5be-8e86-4f50-a35a-e21d7933ce44

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
/-- If the retained selector is false on the distinguished face, its
product times a selected product on that face is the product selected by
the overwritten exponent. -/
theorem solution
    {k N : ℕ}
    (ν : ZMod N → ℝ) (j : Fin k)
    (face : BooleanCube (DeletedCube k j))
    (other : LinearFormsExponent k)
    (hother : ∀ ω, other j ω = false)
    (x : CubePoint k N) :
    cubeSelectedProduct
          (fun ω => faceFactorFamily k N ν j ω x) face *
        linearFormsProduct k N ν other x =
      linearFormsProduct k N ν
        (overwriteFaceExponent j face other) x := by
  rw [faceSelectedProduct_eq_linearFormsProduct]
  unfold linearFormsProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro ω _hω
  by_cases hij : i = j
  · subst i
    simp [faceLinearFormsExponent, overwriteFaceExponent,
      hother]
  · simp [faceLinearFormsExponent, overwriteFaceExponent, hij]
