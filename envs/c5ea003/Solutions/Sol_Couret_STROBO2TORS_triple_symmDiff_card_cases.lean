-- Prove2me | solution 1 for Couret.STROBO2TORS.triple_symmDiff_card_cases
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:54.697768+00:00
-- url     : https://prove2.me/submissions/a91c6e2f-95d7-4627-92f1-81f11e43e020

import Aesop
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_balance
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











/-- Distinct triples have symmetric difference of cardinality two, four or six. -/
theorem p2m_local_triple_symmDiff_card_cases
    (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3) (hST : S ≠ T) :
    (S ∆ T).card = 2 ∨ (S ∆ T).card = 4 ∨ (S ∆ T).card = 6 := by
  have hbalance := triple_symmDiff_card_balance S T hS hT
  have hpos := Finset.card_pos.mpr (Finset.symmDiff_nonempty.mpr hST)
  omega

end FiniteSets

variable {G : Type*} [AddCommGroup G] [DecidableEq G]












end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} α] (S T : Finset.{p2m_u_0} α),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} α S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat (@Finset.card.{p2m_u_0} α T) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      @Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} α) S T →
        Or
          (@Eq.{1} Nat
            (@Finset.card.{p2m_u_0} α
              (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} α)
                (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} α)
                  (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} α) (@Finset.instLattice.{p2m_u_0} α inst)))
                (@Finset.instSDiff.{p2m_u_0} α inst) S T))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Or
            (@Eq.{1} Nat
              (@Finset.card.{p2m_u_0} α
                (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} α)
                  (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} α)
                    (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} α) (@Finset.instLattice.{p2m_u_0} α inst)))
                  (@Finset.instSDiff.{p2m_u_0} α inst) S T))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@Eq.{1} Nat
              (@Finset.card.{p2m_u_0} α
                (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} α)
                  (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} α)
                    (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} α) (@Finset.instLattice.{p2m_u_0} α inst)))
                  (@Finset.instSDiff.{p2m_u_0} α inst) S T))
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))) := @_root_.Couret.STROBO2TORS.p2m_local_triple_symmDiff_card_cases

