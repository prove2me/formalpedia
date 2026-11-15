-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.faceCenteredProduct_insertNth
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:25:00.184196+00:00
-- url     : https://prove2.me/submissions/2c35e280-b49f-43f7-afc8-b90696744425

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_apLinearForm_insertNth_deletedCubeEquiv

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section






/-!
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl















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

open Wikipedia.SzemeredisTheorem in
/-- The centered product on a fixed face, after deleting the irrelevant
coordinate, is a weighted cube-vertex product on `Fin n`. -/
theorem solution
    (n N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (y : Fin n → Bool → ZMod N) :
    faceCenteredProduct (n + 1) N ν j
        (Fin.insertNth j a y) =
      ∏ ω : Fin n → Bool,
        (ν (∑ t : Fin n,
          ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
            ZMod N) * y t (ω t))) - 1) := by
  unfold faceCenteredProduct
  apply Fintype.prod_equiv (deletedCubeEquiv j).symm
  intro ω
  have hform :
      apLinearForm (n + 1) N j ω
          (Fin.insertNth j a y) =
        ∑ t : Fin n,
          ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
            ZMod N) *
              y t ((deletedCubeEquiv j).symm ω t)) := by
    simpa using
      apLinearForm_insertNth_deletedCubeEquiv
        n N j a y ((deletedCubeEquiv j).symm ω)
  rw [hform]
