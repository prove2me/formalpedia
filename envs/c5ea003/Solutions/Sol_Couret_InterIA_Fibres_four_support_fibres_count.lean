-- Prove2me | solution 1 for Couret.InterIA.Fibres.four_support_fibres_count
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:23.769603+00:00
-- url     : https://prove2.me/submissions/b3952d84-3f84-4101-a3b0-452f92d846e8

import Definitions.Def_Couret_AntipodalFibres_0fc966ab17b4
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

















theorem p2m_local_four_support_fibres_count (h : G) (hh : h ≠ 0) (hh2 : h+h=0)
    (S T : Finset G) (hS : S.card=4) (hT : T.card=4)
    (hstable : ∀ x ∈ symmDiff S T, x+h ∈ symmDiff S T) :
    (fibres h (symmDiff S T)).card = 4-(S ∩ T).card := by
  have hc := twice_fibres_card h hh hh2 (symmDiff S T) hstable
  have h1 := Finset.card_sdiff_add_card_inter S T
  have h2 := Finset.card_sdiff_add_card_inter T S
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have he : symmDiff S T = (S \ T) ∪ (T \ S) := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
  have hD : (symmDiff S T).card = (S \ T).card+(T \ S).card := by
    rw [he,Finset.card_union_of_disjoint hd]
  rw [hD] at hc
  rw [Finset.inter_comm T S] at h2
  omega



end Couret.InterIA.Fibres

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (h : G),
  @Ne.{p2m_u_0 + 1} G h
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
    @Eq.{p2m_u_0 + 1} G
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          h h)
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      ∀ (S T : Finset.{p2m_u_0} G),
        @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          @Eq.{1} Nat (@Finset.card.{p2m_u_0} G T) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            (∀ (x : G),
                @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G
                      (@Finset.instSetLike.{p2m_u_0} G))
                    (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                      (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                        (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G)
                          (@Finset.instLattice.{p2m_u_0} G inst_1)))
                      (@Finset.instSDiff.{p2m_u_0} G inst_1) S T)
                    x →
                  @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G
                      (@Finset.instSetLike.{p2m_u_0} G))
                    (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                      (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                        (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G)
                          (@Finset.instLattice.{p2m_u_0} G inst_1)))
                      (@Finset.instSDiff.{p2m_u_0} G inst_1) S T)
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      x h)) →
              @Eq.{1} Nat
                (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
                  (@Couret.InterIA.Fibres.fibres.{p2m_u_0} G inst inst_1 h
                    (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                      (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                        (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G)
                          (@Finset.instLattice.{p2m_u_0} G inst_1)))
                      (@Finset.instSDiff.{p2m_u_0} G inst_1) S T)))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@Finset.card.{p2m_u_0} G
                    (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) S T))) := @_root_.Couret.InterIA.Fibres.p2m_local_four_support_fibres_count

