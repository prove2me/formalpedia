-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.apLinearForm_insertNth_deletedCubeEquiv
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:18:05.852129+00:00
-- url     : https://prove2.me/submissions/02b14130-3163-476f-b328-4ea58c661329

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



@[simp]
theorem deletedCubeEquiv_apply_succAbove
    {n : ℕ} (j : Fin (n + 1))
    (ω : Fin n → Bool) (t : Fin n) :
    deletedCubeEquiv j ω (finSuccAboveEquiv j t) = ω t := by
  simp [deletedCubeEquiv]





































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
/-- After inserting the irrelevant coordinate `j` and canonically
reindexing the deleted cube, a face form is the expected weighted coordinate
sum. -/
theorem solution
    (n N : ℕ) (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (y : Fin n → Bool → ZMod N)
    (ω : Fin n → Bool) :
    apLinearForm (n + 1) N j (deletedCubeEquiv j ω)
        (Fin.insertNth j a y) =
      ∑ t : Fin n,
        ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
          ZMod N) * y t (ω t)) := by
  unfold apLinearForm
  symm
  exact Fintype.sum_equiv (Wikipedia.SzemeredisTheorem.finSuccAboveEquiv j)
    (fun t : Fin n =>
      ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
        ZMod N) * y t (ω t)))
    (fun i : {i : Fin (n + 1) // i ≠ j} =>
      ((((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) *
        ((Fin.insertNth j a y :
          Fin (n + 1) → Bool → ZMod N) i.1)
          (deletedCubeEquiv j ω i)))
    (fun t => by simp)
