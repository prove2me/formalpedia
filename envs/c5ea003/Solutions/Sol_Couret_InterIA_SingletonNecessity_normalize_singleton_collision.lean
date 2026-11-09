-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.normalize_singleton_collision
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:28.621748+00:00
-- url     : https://prove2.me/submissions/2798c0dd-b695-4f33-a70c-7f1045f31958

import Definitions.Def_Couret_SingletonNormalization_99875800f8c3
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
import Definitions.Def_Couret_AbelianBoundary_ad32094cf511

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]



theorem translate_card (A : Finset G) (p : G) :
    (translate A p).card = A.card := by
  exact Finset.card_image_of_injective A (fun _ _ h => sub_left_inj.mp h)

theorem orderedSquare_translate_at (A : Finset G) (p z : G) :
    orderedSquare (translate A p) (z-(p+p)) = orderedSquare A z := by
  have hinj : Function.Injective (fun x : G => x-p) := fun _ _ h => sub_left_inj.mp h
  simp only [translate,orderedSquare,Finset.sum_image (fun _ _ _ _ h => hinj h)]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have he : (a-p)+(b-p)=z-(p+p) ↔ a+b=z := by
    rw [show (a-p)+(b-p)=(a+b)-(p+p) by abel]
    exact sub_left_inj
  simp only [he]

theorem collision_translate (A B : Finset G) (p : G)
    (h : ∀ z, orderedSquare A z=orderedSquare B z) :
    ∀ z, orderedSquare (translate A p) z=orderedSquare (translate B p) z := by
  intro z
  have hz : (z+(p+p))-(p+p)=z := add_sub_cancel_right z (p+p)
  rw [← hz,orderedSquare_translate_at,orderedSquare_translate_at,h]

theorem translate_inter_singleton (A B : Finset G) (p : G)
    (h : A ∩ B = {p}) : translate A p ∩ translate B p = {0} := by
  have hinj : Function.Injective (fun x : G => x-p) := fun _ _ he => sub_left_inj.mp he
  rw [translate,translate,← Finset.image_inter _ _ hinj,h]
  simp

theorem p2m_local_normalize_singleton_collision (A B : Finset G)
    (ha : A.card=4) (hb : B.card=4) (hi : (A ∩ B).card=1)
    (hc : ∀ z, orderedSquare A z=orderedSquare B z) :
    ∃ A₀ B₀ : Finset G, A₀.card=4 ∧ B₀.card=4 ∧ A₀ ∩ B₀={0} ∧
      (∀ z, orderedSquare A₀ z=orderedSquare B₀ z) := by
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hi
  exact ⟨translate A p,translate B p,by rw [translate_card,ha],
    by rw [translate_card,hb],translate_inter_singleton A B p hp,
    collision_translate A B p hc⟩

end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (A B : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G A) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Eq.{1} Nat (@Finset.card.{p2m_u_0} G B) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      @Eq.{1} Nat
          (@Finset.card.{p2m_u_0} G
            (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) A B))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        (∀ (z : G),
            @Eq.{1} Nat (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 A z)
              (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 B z)) →
          @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun A₀ =>
            @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun B₀ =>
              And
                (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G A₀)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (And
                  (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G B₀)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (And
                    (@Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                      (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) A₀ B₀)
                      (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                        (@Finset.instSingleton.{p2m_u_0} G)
                        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                          (@Zero.toOfNat0.{p2m_u_0} G
                            (@NegZeroClass.toZero.{p2m_u_0} G
                              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))))
                    (∀ (z : G),
                      @Eq.{1} Nat (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 A₀ z)
                        (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 B₀ z)))) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_normalize_singleton_collision

