-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_canonical_bank_optimal
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:31.681113+00:00
-- url     : https://prove2.me/submissions/61decfbf-50ce-4257-9b31-840e654e79d1

import Aesop
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_primary_observation_injective
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_product_torsion_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_no_short_reconstructing_bank
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a
import Definitions.Def_Couret_RecohCyclicCoordinates_d669b2caaf1a
import Mathlib.Data.Multiset.Sort
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option autoImplicit false

/-!
Coordinate primary characters and executable exponent encodings for finite
products of cyclic groups. The encoding sorts the multiset of coordinate
values, so multiplicities are retained and no enumeration of the ambient
group is used. Complex roots and characters are semantic objects; exponent
lists and primary-factor data are the inputs used by the exact backend.
-/

namespace Couret.STROBO2TORS





variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]























































/-- On the branch with an even factor and at least three group elements,
the constructed coordinate bank has exactly the optimal slot count. -/
theorem p2m_local_recoh_cyclic_canonical_bank_optimal
    (heven : ∃ i : Fin d, 2 ∣ q i)
    (hG3 : 3 ≤ Fintype.card ((i : Fin d) → ZMod (q i))) :
    Function.Injective
      (fun S : {S : Finset ((j : Fin d) → ZMod (q j)) // S.card = 3} =>
        recohObservation (Sum.elim
          (recohCyclicPrimaryBank q 2 (recohCanonicalPrimaryData q 2))
          (recohCyclicPrimaryBank q 3 (recohCanonicalPrimaryData q 3))) S.1) ∧
    (∀ k : ℕ,
      k < Fintype.card (RecohPrimaryCoordinate q 2) +
        Fintype.card (RecohPrimaryCoordinate q 3) →
      ∀ bank : Fin k → AddChar ((j : Fin d) → ZMod (q j)) ℂ,
        ¬ Function.Injective
          (fun S : {S : Finset ((j : Fin d) → ZMod (q j)) // S.card = 3} =>
            recohObservation bank S.1)) := by
  refine ⟨recoh_cyclic_primary_observation_injective q
    (recohCanonicalPrimaryData q 2) (recohCanonicalPrimaryData q 3), ?_⟩
  intro k hk bank
  have hr : 0 < Fintype.card (RecohPrimaryCoordinate q 2) := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨i, hi⟩ := heven
    exact ⟨⟨i, hi⟩⟩
  exact recoh_no_short_reconstructing_bank _ _ k hr hk
    (recoh_cyclic_product_torsion_card q 2)
    (recoh_cyclic_product_torsion_card q 3) hG3 bank



end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)],
  (@Exists.{1} (Fin d) fun i =>
      @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q i)) →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@Fintype.card.{0} ((i : Fin d) → ZMod (q i))
          (@Pi.instFintype.{0, 0} (Fin d) (fun i => ZMod (q i)) (instDecidableEqFin d) (Fin.fintype d) fun a =>
            @ZMod.fintype (q a) (inst a))) →
      And
        (@Function.Injective.{1, 1}
          (@Subtype.{1} (Finset.{0} ((j : Fin d) → ZMod (q j))) fun S =>
            @Eq.{1} Nat (@Finset.card.{0} ((j : Fin d) → ZMod (q j)) S)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (Prod.{0, 0} (((j : Fin d) → ZMod (q j)) → Nat)
            (Sum.{0, 0}
                (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
              Complex))
          fun S =>
          @Couret.STROBO2TORS.recohObservation.{0, 0} ((j : Fin d) → ZMod (q j))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            (Sum.{0, 0}
              (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (@Sum.elim.{0, 0, 1}
              (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
                (@SubNegMonoid.toAddMonoid.{0} ((j : Fin d) → ZMod (q j))
                  (@AddGroup.toSubNegMonoid.{0} ((j : Fin d) → ZMod (q j))
                    (@AddCommGroup.toAddGroup.{0} ((j : Fin d) → ZMod (q j))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i)))))))
                Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
              (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Nat.fact_prime_two
                (@Couret.STROBO2TORS.recohCanonicalPrimaryData d q inst
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Nat.fact_prime_two))
              (@Couret.STROBO2TORS.recohCyclicPrimaryBank d q
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Nat.fact_prime_three
                (@Couret.STROBO2TORS.recohCanonicalPrimaryData d q inst
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) Nat.fact_prime_three)))
            (@Subtype.val.{1} (Finset.{0} ((j : Fin d) → ZMod (q j)))
              (fun S =>
                @Eq.{1} Nat (@Finset.card.{0} ((j : Fin d) → ZMod (q j)) S)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              S))
        (∀ (k : Nat),
          @LT.lt.{0} Nat instLTNat k
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@Fintype.card.{0}
                  (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Subtype.fintype.{0} (Fin d)
                    (fun i =>
                      @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q i))
                    (fun a => Nat.decidable_dvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q a))
                    (Fin.fintype d)))
                (@Fintype.card.{0}
                  (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@Subtype.fintype.{0} (Fin d)
                    (fun i =>
                      @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (q i))
                    (fun a => Nat.decidable_dvd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (q a))
                    (Fin.fintype d)))) →
            ∀
              (bank :
                Fin k →
                  @AddChar.{0, 0} ((j : Fin d) → ZMod (q j))
                    (@Pi.addMonoid.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                      @AddMonoidWithOne.toAddMonoid.{0} (ZMod (q i))
                        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (q i))
                          (@Ring.toAddGroupWithOne.{0} (ZMod (q i))
                            (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))))
                    Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
              Not
                (@Function.Injective.{1, 1}
                  (@Subtype.{1} (Finset.{0} ((j : Fin d) → ZMod (q j))) fun S =>
                    @Eq.{1} Nat (@Finset.card.{0} ((j : Fin d) → ZMod (q j)) S)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (Prod.{0, 0} (((j : Fin d) → ZMod (q j)) → Nat) (Fin k → Complex)) fun S =>
                  @Couret.STROBO2TORS.recohObservation.{0, 0} ((j : Fin d) → ZMod (q j))
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun j => ZMod (q j)) fun i =>
                      @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                    (fun a b =>
                      @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                        (Fin.fintype d) a b)
                    (Fin k) bank
                    (@Subtype.val.{1} (Finset.{0} ((j : Fin d) → ZMod (q j)))
                      (fun S =>
                        @Eq.{1} Nat (@Finset.card.{0} ((j : Fin d) → ZMod (q j)) S)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      S))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_canonical_bank_optimal

