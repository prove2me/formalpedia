-- Prove2me | solution 1 for Couret.CayleyDoublet.noIso_of_two_colours
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:32:35.365925+00:00
-- url     : https://prove2.me/submissions/eb7ea7c7-021c-4f0a-aec0-c3b629a0c896

import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_doubletArc_iff
import Theorems.Thm_Couret_CayleyDoublet_halfTurn_isMate
import Theorems.Thm_Couret_CayleyDoublet_halfTurn_unique_of_order_three
import Theorems.Thm_Couret_CayleyDoublet_markedArc_iff_pair
import Theorems.Thm_Couret_CayleyDoublet_singleton_step_preserved
import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1

set_option autoImplicit false

/-!
CAYLEY-TWO-COLOUR-FAMILY (14 October 2026).

A directed-graph obstruction derived from *both* intrinsic arc colours.
The universal algebraic theorem is independent of cyclic labels. The
specific ZMod arithmetic is kept in a separate section below. This is an
internal Lean candidate pending a matching-SHA CI compilation.
No academic originality, publication or external review claim.
-/

namespace Couret.CayleyDoublet

section TwoColourObstruction

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



/-- If the marked increment is a natural multiple of the intrinsic
singleton increment, distinct target marked increments prevent an
isomorphism. No quotient labels are assumed to be preserved by f. -/
theorem p2m_local_noIso_of_two_colours
    (a b c h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hab : a ≠ b) (habh : a ≠ b + h)
    (hac : a ≠ c) (hach : a ≠ c + h)
    (hthreeT : (a - c) + (a - c) + (a - c) = 0 ∨
      (a - c) + (a - c) + (a - c) = h)
    (k : ℕ) (hbk : b = k • a)
    (hbc : b ≠ c) (hbch : b ≠ c + h)
    (f : G ≃ G)
    (hf : ∀ x y, CayleyArc (TripleSupport a b h) x y ↔
      CayleyArc (TripleSupport a c h) (f x) (f y)) : False := by
  have hstep : ∀ x : G, f (x + a) = f x + a :=
    singleton_step_preserved a b c h hhalf hne
      hab habh hac hach hthreeT f hf
  have hiter : ∀ n : ℕ, ∀ x : G,
      f (x + n • a) = f x + n • a := by
    intro n
    induction n with
    | zero =>
      intro x
      simp
    | succ n ih =>
      intro x
      have hsmul : (n + 1) • a = n • a + a := by
        simp [add_nsmul]
      calc
        f (x + (n + 1) • a) = f ((x + n • a) + a) := by rw [hsmul]; congr 1; abel
        _ = f (x + n • a) + a := hstep _
        _ = (f x + n • a) + a := by rw [ih x]
        _ = f x + (n + 1) • a := by rw [hsmul]; abel
  let x : G := 0
  have hs : DoubletArc (CayleyArc (TripleSupport a b h))
      (fun z => z + h) x (x + b) :=
    (markedArc_iff_pair a b h hhalf hne hab habh x (x + b)).mpr (Or.inl rfl)
  have hmS : ∀ z, IsMate (CayleyArc (TripleSupport a b h)) z (z + h) :=
    fun z => halfTurn_isMate a b h hhalf hne z
  have hc0 : a - c ≠ 0 := by
    intro he
    exact hac (sub_eq_zero.mp he)
  have hch : a - c ≠ h := by
    intro he
    apply hach
    calc
      a = (a - c) + c := by abel
      _ = h + c := by rw [he]
      _ = c + h := by abel
  have hmT : ∀ z w, IsMate (CayleyArc (TripleSupport a c h)) z w →
      w = z + h := by
    intro z w hw
    exact (halfTurn_unique_of_order_three a c h hhalf hne
      hc0 hch hthreeT z w).mp hw
  have ht := (doubletArc_iff f
    (CayleyArc (TripleSupport a b h)) (CayleyArc (TripleSupport a c h))
    hf (fun z => z + h) (fun z => z + h) hmS hmT x (x + b)).mp hs
  have hfb : f (x + b) = f x + b := by
    calc
      f (x + b) = f (x + k • a) := by rw [hbk]
      _ = f x + k • a := hiter k x
      _ = f x + b := by rw [hbk]
  have hpair := (markedArc_iff_pair a c h hhalf hne hac hach
    (f x) (f (x + b))).mp ht
  rw [hfb] at hpair
  rcases hpair with h1 | h2
  · exact hbc (add_left_cancel h1)
  · exact hbch (add_left_cancel h2)


end TwoColourObstruction

end Couret.CayleyDoublet

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (a b c h : G),
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
    @Ne.{p2m_u_0 + 1} G h
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Ne.{p2m_u_0 + 1} G a b →
        @Ne.{p2m_u_0 + 1} G a
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              b h) →
          @Ne.{p2m_u_0 + 1} G a c →
            @Ne.{p2m_u_0 + 1} G a
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  c h) →
              Or
                  (@Eq.{p2m_u_0 + 1} G
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHSub.{p2m_u_0} G
                            (@SubNegMonoid.toSub.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                          a c)
                        (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHSub.{p2m_u_0} G
                            (@SubNegMonoid.toSub.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                          a c))
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a c))
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                  (@Eq.{p2m_u_0 + 1} G
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHSub.{p2m_u_0} G
                            (@SubNegMonoid.toSub.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                          a c)
                        (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHSub.{p2m_u_0} G
                            (@SubNegMonoid.toSub.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                          a c))
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a c))
                    h) →
                ∀ (k : Nat),
                  @Eq.{p2m_u_0 + 1} G b
                      (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat G G
                        (@instHSMul.{0, p2m_u_0} Nat G
                          (@AddMonoid.toNSMul.{p2m_u_0} G
                            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                        k a) →
                    @Ne.{p2m_u_0 + 1} G b c →
                      @Ne.{p2m_u_0 + 1} G b
                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                            (@instHAdd.{p2m_u_0} G
                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                            c h) →
                        ∀ (f : Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G),
                          (∀ (x y : G),
                              Iff
                                (@Couret.CayleyDoublet.CayleyArc.{p2m_u_0} G inst
                                  (@Couret.CayleyDoublet.TripleSupport.{p2m_u_0} G inst inst_1 a b h) x y)
                                (@Couret.CayleyDoublet.CayleyArc.{p2m_u_0} G inst
                                  (@Couret.CayleyDoublet.TripleSupport.{p2m_u_0} G inst inst_1 a c h)
                                  (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1}
                                    (Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G) G (fun x => G)
                                    (@EquivLike.toFunLike.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1}
                                      (Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G) G G
                                      (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_0 + 1} G G))
                                    f x)
                                  (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1}
                                    (Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G) G (fun x => G)
                                    (@EquivLike.toFunLike.{p2m_u_0 + 1, p2m_u_0 + 1, p2m_u_0 + 1}
                                      (Equiv.{p2m_u_0 + 1, p2m_u_0 + 1} G G) G G
                                      (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_0 + 1} G G))
                                    f y))) →
                            False := @_root_.Couret.CayleyDoublet.p2m_local_noIso_of_two_colours

