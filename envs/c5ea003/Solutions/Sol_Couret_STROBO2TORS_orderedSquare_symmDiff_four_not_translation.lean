-- Prove2me | solution 1 for Couret.STROBO2TORS.orderedSquare_symmDiff_four_not_translation
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:52:47.360935+00:00
-- url     : https://prove2.me/submissions/0f202b28-c933-4e5c-8b52-801b493f761a

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_four_iff
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.SymmDiff

set_option autoImplicit false

/-!
Refinement of the ordered-square classification by symmetric-difference
cardinality. The supports have cardinality three; zero is permitted.
The ambient abelian group need not be finite.
This module classifies the delta=2,4,6 cases; it does not count their pairs.
-/

open scoped symmDiff

namespace Couret.STROBO2TORS

section FiniteSets

variable {α : Type*} [DecidableEq α]













end FiniteSets

variable {G : Type*} [AddCommGroup G] [DecidableEq G]









/-- Equal-square triples with delta four are unrelated by any translation. -/
theorem p2m_local_orderedSquare_symmDiff_four_not_translation
    (S T : Finset G) (hS : S.card = 3) (hT : T.card = 3)
    (hsq : ∀ z, orderedSquare S z = orderedSquare T z)
    (hdelta : (S ∆ T).card = 4) :
    ¬ ∃ v, T = translateSupport S v := by
  have he := ((orderedSquare_symmDiff_four_iff S T hS hT).mp ⟨hsq, hdelta⟩).1
  exact exceptionalPartner_not_any_translation S T hS hT he


end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (S T : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat (@Finset.card.{p2m_u_0} G T) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      (∀ (z : G),
          @Eq.{1} Nat (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S z)
            (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 T z)) →
        @Eq.{1} Nat
            (@Finset.card.{p2m_u_0} G
              (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                  (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instLattice.{p2m_u_0} G inst_1)))
                (@Finset.instSDiff.{p2m_u_0} G inst_1) S T))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          Not
            (@Exists.{p2m_u_0 + 1} G fun v =>
              @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) T
                (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S v)) := @_root_.Couret.STROBO2TORS.p2m_local_orderedSquare_symmDiff_four_not_translation

