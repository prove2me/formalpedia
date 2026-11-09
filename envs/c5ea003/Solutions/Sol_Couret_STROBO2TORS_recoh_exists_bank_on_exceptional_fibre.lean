-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_exists_bank_on_exceptional_fibre
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:28:14.155637+00:00
-- url     : https://prove2.me/submissions/396ef794-45d3-447a-8f3a-2321a1ece295

import Aesop
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_exceptional_normal_form
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_bank_on_param_fibre
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_two_h_iff_exception
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Mathlib.Data.Finite.Card

set_option autoImplicit false

/-!
Character banks chosen after the labelled ordered square has been observed.
The bank may depend on the complete square fibre, but is fixed on that fibre.
The ordinary fibre needs the two-torsion rank many character slots.  An
exceptional fibre needs at most one additional character slot, independently
of the three-torsion rank of the ambient finite abelian group.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]













/-- Every exceptional square fibre admits a bank of `r+1` labelled complex
character coefficients.  The extra character is chosen after the fibre. -/
theorem p2m_local_recoh_exists_bank_on_exceptional_fibre
    (r : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (S : Finset G) (hS : S.card = 3)
    (hexceptional : (squareFibre S).card = 2 * (twoTorsion : Finset G).card) :
    ∃ bank : Fin (r + 1) → AddChar G ℂ,
      Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
        (squareFibre S) := by
  obtain ⟨T, hT⟩ := (squareFibre_card_two_h_iff_exception S hS).mp hexceptional
  obtain ⟨a, d, v, u, hd, hd0, hv, hv0, hu, hs, ht⟩ :=
    recoh_exceptional_normal_form S T hT
  rw [hs]
  exact recoh_exists_bank_on_param_fibre r hcard2 a d v hd hd0 hv hv0



end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (r : Nat),
  @Eq.{1} Nat
      (Nat.card.{p2m_u_0}
        (@Subtype.{p2m_u_0 + 1} G fun x =>
          @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            x))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r) →
    ∀ (S : Finset.{p2m_u_0} G),
      @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        @Eq.{1} Nat
            (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
              (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) →
          @Exists.{p2m_u_0 + 1}
            (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              @AddChar.{p2m_u_0, 0} G
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
            fun bank =>
            @Set.InjOn.{p2m_u_0, 0} (Finset.{p2m_u_0} G)
              (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                Complex)
              (fun T i => @Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) T)
              (@SetLike.coe.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
                (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G))
                (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_exists_bank_on_exceptional_fibre

