-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_three_primary_characters_of_card
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:34.346202+00:00
-- url     : https://prove2.me/submissions/2e7f20ff-9870-4780-a229-9d9f87c50288

import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Theorems.Thm_Couret_STROBO2TORS_recoh_primary_characters_of_subgroup_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_torsion_subgroup_nsmul
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality

set_option autoImplicit false

/-!
Primary complex character banks for finite abelian groups.

The construction takes coordinates on the subgroup killed by a prime p,
extends their standard complex characters to G, then raises each extension
to the factor of |G| coprime to p.  This gives p-primary characters without
assuming that G itself has exponent p.  All existence statements below are
proved from group structure and cardinality; separation is a conclusion.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G]









variable [Fintype G]









/-- The primary bank exists for the actual subgroup `G[p]`, with no
separation or extension hypotheses. -/
theorem recoh_primary_characters_of_card
    (p r : ℕ) [Fact p.Prime]
    (hcard : Nat.card (recohTorsionSubgroup (G := G) p) = p ^ r) :
    ∃ bank : Fin r → AddChar G ℂ,
      (∀ i x, (bank i x) ^ (p ^ (Fintype.card G).factorization p) = 1) ∧
      (∀ x : G, p • x = 0 → (∀ i, bank i x = 1) → x = 0) := by
  obtain ⟨bank, hprimary, hsep⟩ :=
    recoh_primary_characters_of_subgroup_card p r
      (recohTorsionSubgroup (G := G) p)
      (recoh_torsion_subgroup_nsmul p) hcard
  refine ⟨bank, hprimary, ?_⟩
  intro x hx hbank
  exact congrArg (fun a : recohTorsionSubgroup (G := G) p => (a : G))
    (hsep ⟨x, hx⟩ hbank)





/-- The ternary primary bank separates `G[3]` and is trivial on `G[2]`.
Both properties are consequences of the constructed characters. -/
theorem p2m_local_recoh_three_primary_characters_of_card
    (s : ℕ)
    (hcard : Nat.card (recohTorsionSubgroup (G := G) 3) = 3 ^ s) :
    ∃ bank : Fin s → AddChar G ℂ,
      (∀ i x, ∃ n : ℕ, (bank i x) ^ (3 ^ n) = 1) ∧
      (∀ i x, x + x = 0 → bank i x = 1) ∧
      (∀ x : G, (x + x) + x = 0 → (∀ i, bank i x = 1) → x = 0) := by
  obtain ⟨bank, hprimary, hsep⟩ := recoh_primary_characters_of_card 3 s hcard
  refine ⟨bank, ?_, ?_, ?_⟩
  · intro i x
    exact ⟨(Fintype.card G).factorization 3, hprimary i x⟩
  · intro i x hx
    exact recoh_primary_character_trivial_of_coprime 3 2
      ((Fintype.card G).factorization 3) (by decide) (bank i) (hprimary i) x
      (by simpa only [two_nsmul] using hx)
  · intro x hx hbank
    exact hsep x (by simpa only [succ_nsmul, zero_nsmul, zero_add] using hx) hbank

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [Fintype.{p2m_u_0} G] (s : Nat),
  @Eq.{1} Nat
      (Nat.card.{p2m_u_0}
        (@Subtype.{p2m_u_0 + 1} G fun x =>
          @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            x))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) s) →
    @Exists.{p2m_u_0 + 1}
      (Fin s →
        @AddChar.{p2m_u_0, 0} G
          (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
      fun bank =>
      And
        (∀ (i : Fin s) (x : G),
          @Exists.{1} Nat fun n =>
            @Eq.{1} Complex
              (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                (@instHPow.{0, 0} Complex Nat
                  (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                  (@AddChar.{p2m_u_0, 0} G
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                  G (fun x => Complex)
                  (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                  (bank i) x)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) n))
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
        (And
          (∀ (i : Fin s) (x : G),
            @Eq.{p2m_u_0 + 1} G
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  x x)
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
              @Eq.{1} Complex
                (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                  (@AddChar.{p2m_u_0, 0} G
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                  G (fun x => Complex)
                  (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                  (bank i) x)
                (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
          (∀ (x : G),
            @Eq.{p2m_u_0 + 1} G
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
                    x x)
                  x)
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
              (∀ (i : Fin s),
                  @Eq.{1} Complex
                    (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                      (@AddChar.{p2m_u_0, 0} G
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                      G (fun x => Complex)
                      (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
                        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                        (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                      (bank i) x)
                    (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
                @Eq.{p2m_u_0 + 1} G x
                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                    (@Zero.toOfNat0.{p2m_u_0} G
                      (@NegZeroClass.toZero.{p2m_u_0} G
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_three_primary_characters_of_card

