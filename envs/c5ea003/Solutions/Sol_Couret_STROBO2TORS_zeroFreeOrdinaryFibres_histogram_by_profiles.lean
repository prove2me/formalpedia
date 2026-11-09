-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeOrdinaryFibres_histogram_by_profiles
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:56.566878+00:00
-- url     : https://prove2.me/submissions/a4dd7107-510d-429e-9dab-e88df9b614b3

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
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibresProfile_size_filter_card
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibres_eq_profile_union
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeOrdinaryFibres_filter_card_pos
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

section Finite
variable [Fintype G]

/-- A complete ordinary square fibre has a unique two-torsion profile:
its different triples all have the same value of |S ∩ G[2]|. -/
theorem ordinaryFibresProfile_disjoint (j l : ℕ) (hjl : j ≠ l) :
    Disjoint (ordinaryFibresProfile (G := G) j)
      (ordinaryFibresProfile (G := G) l) := by
  apply Finset.disjoint_left.mpr
  intro F hj hl
  obtain ⟨hOrd, S, hS, hjS⟩ := Finset.mem_filter.mp hj
  obtain ⟨_, T, hT, hlT⟩ := Finset.mem_filter.mp hl
  have heq := ordinaryFibre_inter_twoTorsion_card_constant
    F hOrd S T hS hT
  exact hjl (hjS.symm.trans (heq.trans hlT))





private theorem ordinaryProfile_size_filter_disjoint (j l k : ℕ)
    (hjl : j ≠ l) :
    Disjoint
      ((ordinaryFibresProfile (G := G) j).filter
        (fun F => (withoutZero F).card = k))
      ((ordinaryFibresProfile (G := G) l).filter
        (fun F => (withoutZero F).card = k)) := by
  apply Finset.disjoint_left.mpr
  intro F hj hl
  exact (Finset.disjoint_left.mp
      (ordinaryFibresProfile_disjoint (G := G) j l hjl))
    (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hl).1

/-- The histogram of nonempty ordinary zero-free fibres is the sum of four
profile point masses. The k>0 hypothesis discards genuinely empty restrictions. -/
theorem p2m_local_zeroFreeOrdinaryFibres_histogram_by_profiles (k : ℕ) (hk : 0 < k) :
    ((zeroFreeOrdinaryFibres : Finset (Finset (Finset G))).filter
      (fun F => F.card = k)).card =
      (if (twoTorsion : Finset G).card = k then
        (ordinaryFibresProfile (G := G) 0).card else 0) +
      (if (twoTorsion : Finset G).card - 1 = k then
        (ordinaryFibresProfile (G := G) 1).card else 0) +
      (if (twoTorsion : Finset G).card - 2 = k then
        (ordinaryFibresProfile (G := G) 2).card else 0) +
      (if (twoTorsion : Finset G).card - 3 = k then
        (ordinaryFibresProfile (G := G) 3).card else 0) := by
  rw [zeroFreeOrdinaryFibres_filter_card_pos k hk, ordinaryFibres_eq_profile_union]
  simp only [Finset.filter_union]
  have hd01 := ordinaryProfile_size_filter_disjoint (G := G) 0 1 k (by decide)
  have hd02 := ordinaryProfile_size_filter_disjoint (G := G) 0 2 k (by decide)
  have hd03 := ordinaryProfile_size_filter_disjoint (G := G) 0 3 k (by decide)
  have hd12 := ordinaryProfile_size_filter_disjoint (G := G) 1 2 k (by decide)
  have hd13 := ordinaryProfile_size_filter_disjoint (G := G) 1 3 k (by decide)
  have hd23 := ordinaryProfile_size_filter_disjoint (G := G) 2 3 k (by decide)
  have hd0 : Disjoint
      ((ordinaryFibresProfile (G := G) 0).filter
        (fun F => (withoutZero F).card = k))
      (((ordinaryFibresProfile (G := G) 1).filter
        (fun F => (withoutZero F).card = k)) ∪
       (((ordinaryFibresProfile (G := G) 2).filter
        (fun F => (withoutZero F).card = k)) ∪
        ((ordinaryFibresProfile (G := G) 3).filter
        (fun F => (withoutZero F).card = k)))) := by
    apply Finset.disjoint_left.mpr
    intro F h0 hrest
    rcases Finset.mem_union.mp hrest with h1 | h23
    · exact (Finset.disjoint_left.mp hd01) h0 h1
    · rcases Finset.mem_union.mp h23 with h2 | h3
      · exact (Finset.disjoint_left.mp hd02) h0 h2
      · exact (Finset.disjoint_left.mp hd03) h0 h3
  have hd1 : Disjoint
      ((ordinaryFibresProfile (G := G) 1).filter
        (fun F => (withoutZero F).card = k))
      (((ordinaryFibresProfile (G := G) 2).filter
        (fun F => (withoutZero F).card = k)) ∪
        ((ordinaryFibresProfile (G := G) 3).filter
        (fun F => (withoutZero F).card = k))) := by
    apply Finset.disjoint_left.mpr
    intro F h1 h23
    rcases Finset.mem_union.mp h23 with h2 | h3
    · exact (Finset.disjoint_left.mp hd12) h1 h2
    · exact (Finset.disjoint_left.mp hd13) h1 h3
  rw [Finset.card_union_of_disjoint hd0,
      Finset.card_union_of_disjoint hd1,
      Finset.card_union_of_disjoint hd23,
      ordinaryFibresProfile_size_filter_card 0 k,
      ordinaryFibresProfile_size_filter_card 1 k,
      ordinaryFibresProfile_size_filter_card 2 k,
      ordinaryFibresProfile_size_filter_card 3 k]
  simp only [Nat.sub_zero]
  omega



end Finite
end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) k →
    @Eq.{1} Nat
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Finset.filter.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (fun F => @Eq.{1} Nat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) F) k)
          (fun a => instDecidableEqNat (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) a) k)
          (@Couret.STROBO2TORS.zeroFreeOrdinaryFibres.{p2m_u_0} G inst inst_1 inst_2)))
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
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeOrdinaryFibres_histogram_by_profiles

