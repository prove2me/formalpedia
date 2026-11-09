-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_observation_injective_of_separating_banks
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:08.896296+00:00
-- url     : https://prove2.me/submissions/18ece8db-3470-44a7-b35c-9ff2d83ca601

import Aesop
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_reconstruction_of_separating_banks
import Definitions.Def_Couret_Strobo2TorsEnumeration_d0ac93e4ff30
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
RECOH: reconstructing a cardinality-three support from its labelled ordered
square and a fixed bank of individual complex character coefficients.

The observation and the support cardinality are explicit. The classification
used below is the existing STROBO theorem, not an additional hypothesis.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

















theorem p2m_local_recoh_observation_injective_of_separating_banks
    {I J : Type*} (bank2 : I → AddChar G ℂ) (bank3 : J → AddChar G ℂ)
    (hnonzero : ∀ i : I, ∀ S : Finset G, S.card = 3 →
      recohSupportProbe (bank2 i) S ≠ 0)
    (hsep2 : ∀ u : G, u + u = 0 → (∀ i : I, bank2 i u = 1) → u = 0)
    (htrivial2 : ∀ j : J, ∀ u : G, u + u = 0 → bank3 j u = 1)
    (hsep3 : ∀ v : G, (v + v) + v = 0 → (∀ j : J, bank3 j v = 1) → v = 0) :
    Function.Injective (fun S : {S : Finset G // S.card = 3} =>
      recohObservation (Sum.elim bank2 bank3) S.1) := by
  intro S T h
  apply Subtype.ext
  apply recoh_reconstruction_of_separating_banks bank2 bank3 hnonzero hsep2
    htrivial2 hsep3 S.1 T.1 S.2 T.2
  · exact congrFun (congrArg Prod.fst h)
  · intro i
    exact congrFun (congrArg Prod.snd h) (Sum.inl i)
  · intro j
    exact congrFun (congrArg Prod.snd h) (Sum.inr j)

end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {I : Type p2m_u_1}
  {J : Type p2m_u_2}
  (bank2 :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (bank3 :
    J →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
  (∀ (i : I) (S : Finset.{p2m_u_0} G),
      @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        @Ne.{1} Complex (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank2 i) S)
          (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero))) →
    (∀ (u : G),
        @Eq.{p2m_u_0 + 1} G
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              u u)
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
          (∀ (i : I),
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
                  (bank2 i) u)
                (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
            @Eq.{p2m_u_0 + 1} G u
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))) →
      (∀ (j : J) (u : G),
          @Eq.{p2m_u_0 + 1} G
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                u u)
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
                (bank3 j) u)
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
        (∀ (v : G),
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
                    v v)
                  v)
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
              (∀ (j : J),
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
                      (bank3 j) v)
                    (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
                @Eq.{p2m_u_0 + 1} G v
                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                    (@Zero.toOfNat0.{p2m_u_0} G
                      (@NegZeroClass.toZero.{p2m_u_0} G
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))) →
          @Function.Injective.{p2m_u_0 + 1, max ((max p2m_u_2 p2m_u_1) + 1) (p2m_u_0 + 1)}
            (@Subtype.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun S =>
              @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (Prod.{p2m_u_0, max p2m_u_2 p2m_u_1} (G → Nat) (Sum.{p2m_u_1, p2m_u_2} I J → Complex)) fun S =>
            @Couret.STROBO2TORS.recohObservation.{p2m_u_0, max p2m_u_2 p2m_u_1} G inst inst_1
              (Sum.{p2m_u_1, p2m_u_2} I J)
              (@Sum.elim.{p2m_u_1, p2m_u_2, p2m_u_0 + 1} I J
                (@AddChar.{p2m_u_0, 0} G
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                  Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                bank2 bank3)
              (@Subtype.val.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                (fun S =>
                  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_observation_injective_of_separating_banks

