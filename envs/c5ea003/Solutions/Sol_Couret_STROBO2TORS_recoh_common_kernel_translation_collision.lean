-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_common_kernel_translation_collision
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:37.132922+00:00
-- url     : https://prove2.me/submissions/1c63f337-d84b-4204-b0dd-b00dde40cf36

import Aesop
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_triple_probe_translate
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_free_of_card_three
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
RECOH: character masks and genuine translation witnesses.
A dependency of the prospective universal bank bound B(G)=r+s.
No Fourier character-existence or full rank theorem is asserted here.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]







/-- A nontrivial involution invisible to every probe gives an actual
collision of distinct triples, preserving all nine labelled sums.
This is separate from, and complementary to, three-torsion reflection. -/
theorem p2m_local_recoh_common_kernel_translation_collision
    {R : Type*} [CommRing R]
    (a b c d : G)
    (hcard : ({a, b, c} : Finset G).card = 3)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (bank : List (G → R))
    (hadd : ∀ chi ∈ bank, ∀ x y : G, chi (x + y) = chi x * chi y)
    (htrivial : ∀ chi ∈ bank, chi d = 1) :
    (({a, b, c} : Finset G) ≠ {a + d, b + d, c + d}) ∧
      (∀ z : G, orderedSquare ({a, b, c} : Finset G) z =
        orderedSquare ({a + d, b + d, c + d} : Finset G) z) ∧
      (∀ chi ∈ bank, recohTripleProbe chi a b c =
        recohTripleProbe chi (a + d) (b + d) (c + d)) := by
  have hne : translateSupport ({a, b, c} : Finset G) d ≠
      ({a, b, c} : Finset G) := by
    intro heq
    exact hd0 (translateSupport_free_of_card_three
      ({a, b, c} : Finset G) hcard d hd heq)
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    apply hne
    simpa only [translateSupport_three] using heq.symm
  · intro z
    have hsq := orderedSquare_translate_of_card_three
      ({a, b, c} : Finset G) hcard d z hd
    rw [translateSupport_three] at hsq
    exact hsq.symm
  · intro chi hchi
    have hp := recoh_triple_probe_translate chi (hadd chi hchi) a b c d
    rw [htrivial chi hchi] at hp
    simpa using hp.symm

end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {R : Type p2m_u_1}
  [inst_2 : CommRing.{p2m_u_1} R] (a b c d : G),
  @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} G
        (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) a
          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) b
            (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instSingleton.{p2m_u_0} G) c))))
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{p2m_u_0 + 1} G
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          d d)
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Ne.{p2m_u_0 + 1} G d
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
        ∀ (bank : List.{max p2m_u_0 p2m_u_1} (G → R)),
          (∀ (chi : G → R),
              @Membership.mem.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1} (G → R) (List.{max p2m_u_0 p2m_u_1} (G → R))
                  (@List.instMembership.{max p2m_u_0 p2m_u_1} (G → R)) bank chi →
                ∀ (x y : G),
                  @Eq.{p2m_u_1 + 1} R
                    (chi
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        x y))
                    (@HMul.hMul.{p2m_u_1, p2m_u_1, p2m_u_1} R R R
                      (@instHMul.{p2m_u_1} R
                        (@Distrib.toMul.{p2m_u_1} R
                          (@instDistribOfSemiring.{p2m_u_1} R
                            (@CommSemiring.toSemiring.{p2m_u_1} R (@CommRing.toCommSemiring.{p2m_u_1} R inst_2)))))
                      (chi x) (chi y))) →
            (∀ (chi : G → R),
                @Membership.mem.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1} (G → R) (List.{max p2m_u_0 p2m_u_1} (G → R))
                    (@List.instMembership.{max p2m_u_0 p2m_u_1} (G → R)) bank chi →
                  @Eq.{p2m_u_1 + 1} R (chi d)
                    (@OfNat.ofNat.{p2m_u_1} R (nat_lit 1)
                      (@One.toOfNat1.{p2m_u_1} R
                        (@AddMonoidWithOne.toOne.{p2m_u_1} R
                          (@AddGroupWithOne.toAddMonoidWithOne.{p2m_u_1} R
                            (@Ring.toAddGroupWithOne.{p2m_u_1} R (@CommRing.toRing.{p2m_u_1} R inst_2))))))) →
              And
                (@Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                  (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) a
                    (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1) b
                      (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                        (@Finset.instSingleton.{p2m_u_0} G) c)))
                  (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      a d)
                    (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (@Finset.instInsert.{p2m_u_0} G inst_1)
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        b d)
                      (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                        (@Finset.instSingleton.{p2m_u_0} G)
                        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                          (@instHAdd.{p2m_u_0} G
                            (@AddCommMagma.toAdd.{p2m_u_0} G
                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                          c d)))))
                (And
                  (∀ (z : G),
                    @Eq.{1} Nat
                      (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                        (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                          (@Finset.instInsert.{p2m_u_0} G inst_1) a
                          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                            (@Finset.instInsert.{p2m_u_0} G inst_1) b
                            (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                              (@Finset.instSingleton.{p2m_u_0} G) c)))
                        z)
                      (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1
                        (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                          (@Finset.instInsert.{p2m_u_0} G inst_1)
                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                            (@instHAdd.{p2m_u_0} G
                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                            a d)
                          (@Insert.insert.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                            (@Finset.instInsert.{p2m_u_0} G inst_1)
                            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                              (@instHAdd.{p2m_u_0} G
                                (@AddCommMagma.toAdd.{p2m_u_0} G
                                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                      (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                              b d)
                            (@Singleton.singleton.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                              (@Finset.instSingleton.{p2m_u_0} G)
                              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                                (@instHAdd.{p2m_u_0} G
                                  (@AddCommMagma.toAdd.{p2m_u_0} G
                                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                                c d))))
                        z))
                  (∀ (chi : G → R),
                    @Membership.mem.{max p2m_u_0 p2m_u_1, max p2m_u_0 p2m_u_1} (G → R)
                        (List.{max p2m_u_0 p2m_u_1} (G → R)) (@List.instMembership.{max p2m_u_0 p2m_u_1} (G → R)) bank
                        chi →
                      @Eq.{p2m_u_1 + 1} R (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_1} G R inst_2 chi a b c)
                        (@Couret.STROBO2TORS.recohTripleProbe.{p2m_u_0, p2m_u_1} G R inst_2 chi
                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                            (@instHAdd.{p2m_u_0} G
                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                            a d)
                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                            (@instHAdd.{p2m_u_0} G
                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                            b d)
                          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                            (@instHAdd.{p2m_u_0} G
                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                            c d)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_common_kernel_translation_collision

