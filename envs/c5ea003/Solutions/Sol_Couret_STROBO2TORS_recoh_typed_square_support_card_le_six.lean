-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_typed_square_support_card_le_six
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:22.891473+00:00
-- url     : https://prove2.me/submissions/f6f66f80-b44f-4342-8b16-bc4c96302b9e

import Aesop
import Definitions.Def_Couret_RecohTypedObservation_b23b2e33136b
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72

set_option autoImplicit false

/-!
Typed sparse input for the labelled ordered convolution square.

The coefficient function and its covering finite set are constructed from
the same list of position/count entries.  Their consistency is proved,
rather than supplied to the decoder.  The format validator expresses the
numeric checks performed by the Python square reader after coordinates and
integers have been parsed.  Syntactic JSON parsing is not part of this file.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [DecidableEq G]

















theorem p2m_local_recoh_typed_square_support_card_le_six
    (entries : List (G × ℕ)) (h : RecohTypedSquareFormat entries) :
    (recohTypedSquareSupport entries).card ≤ 6 := by
  exact (List.toFinset_card_le (entries.map Prod.fst)).trans
    (by simpa only [List.length_map] using h.2.1)





end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} G] (entries : List.{p2m_u_0} (Prod.{p2m_u_0, 0} G Nat)),
  @Couret.STROBO2TORS.RecohTypedSquareFormat.{p2m_u_0} G entries →
    @LE.le.{0} Nat instLENat
      (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.recohTypedSquareSupport.{p2m_u_0} G inst entries))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_typed_square_support_card_le_six

