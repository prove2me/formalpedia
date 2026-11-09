-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.singleton_collision_iff_contains_c4_square
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:22:36.008508+00:00
-- url     : https://prove2.me/submissions/b9e92bdd-a7d6-4441-90c1-bc76f95e5fdc

import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_AbelianBoundary_contains_c4_square_sufficient
import Theorems.Thm_Couret_InterIA_SingletonNecessity_contains_c4_square_of_matching
import Theorems.Thm_Couret_InterIA_SingletonNecessity_cross_count_cancellation
import Theorems.Thm_Couret_InterIA_SingletonNecessity_cross_encoding
import Theorems.Thm_Couret_InterIA_SingletonNecessity_exclusive_enumeration
import Theorems.Thm_Couret_InterIA_SingletonNecessity_fibreParity_of_collision
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixed_count_cancellation
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixed_encoding
import Theorems.Thm_Couret_InterIA_SingletonNecessity_normalize_singleton_collision
import Theorems.Thm_Couret_InterIA_SingletonNecessity_parity_relabel
import Definitions.Def_Couret_MatchingElimination_8675038abe55
import Definitions.Def_Couret_C4SquareAlgebra_06ed7b10cc0e
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Couret.InterIA.Parity Couret.InterIA.AbelianBoundary
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem collision_matching_extraction (x : Fin 6 → G) (hd : SevenDistinct x)
    (hs : ∀ z, orderedSquare (supportLeft x) z=orderedSquare (supportRight x) z) :
    ∃ y : Fin 6 → G, SevenDistinct y ∧ supportLeft y=supportLeft x ∧
      supportRight y=supportRight x ∧
      ((∃ p : List ℕ, p.Perm (List.range 6) ∧ RelationsHold y false p) ∨
       (∃ p : List ℕ, p.Perm (List.range 7) ∧ RelationsHold y true p)) := by
  obtain ⟨y,hy,hyl,hyr,hc|hm⟩ := parity_relabel x hd (fibreParity_of_collision x hd hs)
  · refine ⟨y,hy,hyl,hyr,Or.inl ?_⟩
    exact cross_encoding y hc (cross_count_cancellation y hy hc (by
      simpa only [hyl,hyr] using hs))
  · refine ⟨y,hy,hyl,hyr,Or.inr ?_⟩
    exact mixed_encoding y hm (mixed_count_cancellation y hy hm (by
      simpa only [hyl,hyr] using hs))

theorem contains_c4_square_necessary (A B : Finset G)
    (ha : A.card=4) (hb : B.card=4) (hi : (A ∩ B).card=1)
    (hs : ∀ z, orderedSquare A z=orderedSquare B z) :
    ∃ φ : G4 →+ G, Function.Injective φ := by
  obtain ⟨A₀,B₀,ha₀,hb₀,hi₀,hs₀⟩ := normalize_singleton_collision A B ha hb hi hs
  obtain ⟨x,hd,hl,hr⟩ := exclusive_enumeration A₀ B₀ ha₀ hb₀ hi₀
  have hx : ∀ z, orderedSquare (supportLeft x) z=orderedSquare (supportRight x) z := by
    simpa only [hl,hr] using hs₀
  obtain ⟨y,hy,_,_,hm⟩ := collision_matching_extraction x hd hx
  exact contains_c4_square_of_matching y hy hm

theorem p2m_local_singleton_collision_iff_contains_c4_square :
    (∃ A B : Finset G, A.card=4 ∧ B.card=4 ∧ (A ∩ B).card=1 ∧
      ∀ z, orderedSquare A z=orderedSquare B z) ↔
    (∃ φ : G4 →+ G, Function.Injective φ) := by
  constructor
  · rintro ⟨A,B,ha,hb,hi,hs⟩
    exact contains_c4_square_necessary A B ha hb hi hs
  · rintro ⟨φ,hφ⟩
    exact contains_c4_square_sufficient φ hφ

end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G],
  Iff
    (@Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun A =>
      @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun B =>
        And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G A) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G B) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (And
              (@Eq.{1} Nat
                (@Finset.card.{p2m_u_0} G
                  (@Inter.inter.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instInter.{p2m_u_0} G inst_1) A B))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (∀ (z : G),
                @Eq.{1} Nat (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 A z)
                  (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1 B z)))))
    (@Exists.{p2m_u_0 + 1}
      (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 G
        (@AddZeroClass.toAddZero.{0} Couret.InterIA.AbelianBoundary.G4
          (@Prod.instAddZeroClass.{0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@AddMonoidWithOne.toAddMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@AddGroupWithOne.toAddMonoidWithOne.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))
            (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@AddMonoidWithOne.toAddMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@AddGroupWithOne.toAddMonoidWithOne.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
        (@AddZeroClass.toAddZero.{p2m_u_0} G
          (@AddMonoid.toAddZeroClass.{p2m_u_0} G
            (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
              (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
      fun φ =>
      @Function.Injective.{1, p2m_u_0 + 1} Couret.InterIA.AbelianBoundary.G4 G
        (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
          (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 G
            (@AddZeroClass.toAddZero.{0} Couret.InterIA.AbelianBoundary.G4
              (@Prod.instAddZeroClass.{0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
            (@AddZeroClass.toAddZero.{p2m_u_0} G
              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
          Couret.InterIA.AbelianBoundary.G4 (fun x => G)
          (@AddMonoidHom.instFunLike.{0, p2m_u_0} Couret.InterIA.AbelianBoundary.G4 G
            (@AddZeroClass.toAddZero.{0} Couret.InterIA.AbelianBoundary.G4
              (@Prod.instAddZeroClass.{0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))
                (@AddMonoid.toAddZeroClass.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@AddMonoidWithOne.toAddMonoid.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (@AddGroupWithOne.toAddMonoidWithOne.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                          (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
            (@AddZeroClass.toAddZero.{p2m_u_0} G
              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
          φ)) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_singleton_collision_iff_contains_c4_square

