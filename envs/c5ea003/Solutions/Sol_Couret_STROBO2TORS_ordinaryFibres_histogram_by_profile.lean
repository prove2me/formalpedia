-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryFibres_histogram_by_profile
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:40:37.969042+00:00
-- url     : https://prove2.me/submissions/5317bafd-dbd1-4843-9b20-9a8d66738f07

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibre_inter_twoTorsion_card_constant
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_filter_size_card
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_eq_profile_union_alternative
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite

variable [Fintype G]





/-- Two distinct ordinary profile strata contain no common complete fibre. -/
theorem ordinaryFibresProfile_pair_disjoint (j l : ℕ) (hjl : j ≠ l) :
    Disjoint (ordinaryFibresProfile (G := G) j)
      (ordinaryFibresProfile (G := G) l) := by
  apply Finset.disjoint_left.mpr
  intro F hj hl
  obtain ⟨hOrd, S, hS, hSJ⟩ := Finset.mem_filter.mp hj
  obtain ⟨_, T, hT, hTL⟩ := Finset.mem_filter.mp hl
  have hconst :=
    ordinaryFibre_inter_twoTorsion_card_constant F hOrd S T hS hT
  exact hjl (hSJ.symm.trans (hconst.trans hTL))



/-- Exact ordinary histogram, including the possible zero-size full-fibre
restrictions. This formula is over *full ordinary fibres*; for k>0 it also
counts their observed zero-free images, by the earlier injectivity theorem. -/
theorem p2m_local_ordinaryFibres_histogram_by_profile (k : ℕ) :
    ((ordinaryFibres : Finset (Finset (Finset G))).filter
      (fun F => (withoutZero F).card = k)).card =
      (if (twoTorsion : Finset G).card = k then
        (ordinaryFibresProfile (G := G) 0).card else 0) +
      (if (twoTorsion : Finset G).card - 1 = k then
        (ordinaryFibresProfile (G := G) 1).card else 0) +
      (if (twoTorsion : Finset G).card - 2 = k then
        (ordinaryFibresProfile (G := G) 2).card else 0) +
      (if (twoTorsion : Finset G).card - 3 = k then
        (ordinaryFibresProfile (G := G) 3).card else 0) := by
  let P : ℕ → Finset (Finset (Finset G)) :=
    fun j => (ordinaryFibresProfile (G := G) j).filter
      (fun F => (withoutZero F).card = k)
  have hdisj (j l : ℕ) (hjl : j ≠ l) : Disjoint (P j) (P l) := by
    apply Finset.disjoint_left.mpr
    intro F hj hl
    have hj' : F ∈ ordinaryFibresProfile j := (Finset.mem_filter.mp hj).1
    have hl' : F ∈ ordinaryFibresProfile l := (Finset.mem_filter.mp hl).1
    exact (Finset.disjoint_left.mp (ordinaryFibresProfile_pair_disjoint j l hjl)) hj' hl'
  have h23 : Disjoint (P 2) (P 3) :=
    hdisj 2 3 (by decide)
  have h123 : Disjoint (P 1) (P 2 ∪ P 3) := by
    apply Finset.disjoint_left.mpr
    intro F h1 hrest
    rcases Finset.mem_union.mp hrest with h2 | h3
    · exact (Finset.disjoint_left.mp (hdisj 1 2 (by decide))) h1 h2
    · exact (Finset.disjoint_left.mp (hdisj 1 3 (by decide))) h1 h3
  have h0123 : Disjoint (P 0) (P 1 ∪ (P 2 ∪ P 3)) := by
    apply Finset.disjoint_left.mpr
    intro F h0 hrest
    rcases Finset.mem_union.mp hrest with h1 | h23'
    · exact (Finset.disjoint_left.mp (hdisj 0 1 (by decide))) h0 h1
    · rcases Finset.mem_union.mp h23' with h2 | h3
      · exact (Finset.disjoint_left.mp (hdisj 0 2 (by decide))) h0 h2
      · exact (Finset.disjoint_left.mp (hdisj 0 3 (by decide))) h0 h3
  have hpart :
      ((ordinaryFibres : Finset (Finset (Finset G))).filter
        (fun F => (withoutZero F).card = k)) =
          P 0 ∪ (P 1 ∪ (P 2 ∪ P 3)) := by
    dsimp [P]
    rw [ordinaryFibres_eq_profile_union_alternative]
    simp only [Finset.filter_union]
  calc
    ((ordinaryFibres : Finset (Finset (Finset G))).filter
      (fun F => (withoutZero F).card = k)).card =
        (P 0 ∪ (P 1 ∪ (P 2 ∪ P 3))).card :=
          congrArg Finset.card hpart
    _ = (P 0).card + (P 1).card + (P 2).card + (P 3).card := by
      rw [Finset.card_union_of_disjoint h0123,
        Finset.card_union_of_disjoint h123,
        Finset.card_union_of_disjoint h23]
      omega
    _ = _ := by
      dsimp [P]
      rw [ordinaryFibresProfile_filter_size_card 0 k,
        ordinaryFibresProfile_filter_size_card 1 k,
        ordinaryFibresProfile_filter_size_card 2 k,
        ordinaryFibresProfile_filter_size_card 3 k]
      simp only [Nat.sub_zero]



end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (k : Nat),
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (fun F =>
          @Eq.{1} Nat
            (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 F)) k)
        (fun a =>
          instDecidableEqNat
            (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.withoutZero.{p2m_u_0} G inst inst_1 a)) k)
        (@Couret.STROBO2TORS.ordinaryFibres.{p2m_u_0} G inst inst_1 inst_2)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@ite.{1} Nat
            (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) k)
            (instDecidableEqNat
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)) k)
            (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@ite.{1} Nat
            (@Eq.{1} Nat
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (instDecidableEqNat
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              k)
            (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
              (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (@ite.{1} Nat
          (@Eq.{1} Nat
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            k)
          (instDecidableEqNat
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            k)
          (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
      (@ite.{1} Nat
        (@Eq.{1} Nat
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          k)
        (instDecidableEqNat
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          k)
        (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Couret.STROBO2TORS.ordinaryFibresProfile.{p2m_u_0} G inst inst_1 inst_2
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryFibres_histogram_by_profile

