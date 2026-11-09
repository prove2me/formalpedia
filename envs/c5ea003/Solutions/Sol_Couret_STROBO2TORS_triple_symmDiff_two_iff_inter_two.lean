-- Prove2me | solution 1 for Couret.STROBO2TORS.triple_symmDiff_two_iff_inter_two
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:53:15.493202+00:00
-- url     : https://prove2.me/submissions/e2e65a5e-8497-4f99-89ab-3680fab409cb

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



theorem p2m_local_triple_symmDiff_two_iff_inter_two
    (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3) :
    (S ∆ T).card = 2 ↔ (S ∩ T).card = 2 := by
  have hbalance := triple_symmDiff_card_balance S T hS hT
  omega









end FiniteSets

variable {G : Type*} [AddCommGroup G] [DecidableEq G]












end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} α] (S T : Finset.{p2m_u_0} α),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} α S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat (@Finset.card.{p2m_u_0} α T) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      Iff
        (@Eq.{1} Nat
          (@Finset.card.{p2m_u_0} α
            (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} α)
              (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} α)
                (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} α) (@Finset.instLattice.{p2m_u_0} α inst)))
              (@Finset.instSDiff.{p2m_u_0} α inst) S T))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@Eq.{1} Nat
          (@Finset.card.{p2m_u_0} α
            (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} α) (@Finset.instInter.{p2m_u_0} α inst) S T))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @_root_.Couret.STROBO2TORS.p2m_local_triple_symmDiff_two_iff_inter_two

