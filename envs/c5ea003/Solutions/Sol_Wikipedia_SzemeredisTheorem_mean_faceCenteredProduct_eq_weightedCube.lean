-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_faceCenteredProduct_eq_weightedCube
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:28:17.581198+00:00
-- url     : https://prove2.me/submissions/b05f7bed-0d0b-4263-90af-e4a59354ffc5

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_faceCenteredProduct_insertNth
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_insertNth

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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
/-- Averaging a face centered product discards its irrelevant coordinate and
leaves the weighted cube-vertex average. -/
theorem solution
    (n N : ℕ) [NeZero N] (ν : ZMod N → ℝ)
    (j : Fin (n + 1)) :
    mean (faceCenteredProduct (n + 1) N ν j) =
      mean (fun y : Fin n → Bool → ZMod N =>
        ∏ ω : Fin n → Bool,
          (ν (∑ t : Fin n,
            ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
              ZMod N) * y t (ω t))) - 1)) := by
  calc
    mean (faceCenteredProduct (n + 1) N ν j) =
        mean₂ (fun a : Bool → ZMod N =>
          fun y : Fin n → Bool → ZMod N =>
            faceCenteredProduct (n + 1) N ν j
              (Fin.insertNth j a y)) :=
      mean_insertNth n j _
    _ = mean (fun _a : Bool → ZMod N =>
          mean (fun y : Fin n → Bool → ZMod N =>
            ∏ ω : Fin n → Bool,
              (ν (∑ t : Fin n,
                ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
                  ZMod N) * y t (ω t))) - 1))) := by
      unfold mean₂
      apply congrArg mean
      funext a
      apply congrArg mean
      funext y
      exact faceCenteredProduct_insertNth n N ν j a y
    _ = mean (fun y : Fin n → Bool → ZMod N =>
          ∏ ω : Fin n → Bool,
            (ν (∑ t : Fin n,
              ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
                ZMod N) * y t (ω t))) - 1)) := by
      apply mean_const
