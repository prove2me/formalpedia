-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeSquareDeltaPairCount_divisibility
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:59:20.324008+00:00
-- url     : https://prove2.me/submissions/0bb8c06b-a3e0-44e8-bdae-9dd64f3051fe

import Aesop
import Definitions.Def_Couret_Strobo2TorsZeroFreeDeltaCount_41cbef917dd9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_adj_iff
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_six_twice_edges_numeric
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_eq_translate_iff
import Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_six_twelve_mul_edges
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_adj_iff
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_four_twice_edges_numeric
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_two_four_mul_edges
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_injective
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_symmDiff_card
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_balance
import Theorems.Thm_Couret_STROBO2TORS_zeroFreeGraph_mul_edges
import Definitions.Def_Couret_Strobo2TorsZeroFreeIncidence_e3b7fd015f51

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact unordered collision counts by symmetric difference after excluding zero
from both three-element supports. The proof transfers each translation-stable
branch by incidence counting. All subtractions and divisions are in Nat.
Historical unrestricted counts remain unchanged.
-/

namespace Couret.STROBO2TORS

private theorem zeroFreeDelta_cancel_formula (n u d c z p : ℕ)
    (hn : 0 < n) (hcount : d * c = n * p)
    (htransfer : n * z = (n - u) * c) :
    d * z = (n - u) * p := by
  apply Nat.eq_of_mul_eq_mul_left hn
  calc
    n * (d * z) = d * (n * z) := by ring
    _ = d * ((n - u) * c) := by rw [htransfer]
    _ = (n - u) * (d * c) := by ring
    _ = (n - u) * (n * p) := by rw [hcount]
    _ = n * ((n - u) * p) := by ring

/-- The size of the union is determined by the symmetric difference. -/
theorem triple_union_card_of_symmDiff {α : Type*} [DecidableEq α]
    (S T : Finset α) (hS : S.card = 3) (hT : T.card = 3)
    (k : ℕ) (hk : (S ∆ T).card = k) :
    (S ∪ T).card = 3 + k / 2 := by
  have hbalance := triple_symmDiff_card_balance S T hS hT
  have hunion := Finset.card_union_add_card_inter S T
  omega

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem translateSupport_eq_iff (S T : Finset G) (a : G) :
    translateSupport S a = translateSupport T a ↔ S = T :=
  (translateSupport_injective a).eq_iff

/-- A common arbitrary translation preserves the ordinary partner relation. -/
theorem ordinaryPartner_translate_iff (S T : Finset G) (a : G) :
    OrdinaryPartner (translateSupport S a) (translateSupport T a) ↔
      OrdinaryPartner S T := by
  constructor
  · rintro ⟨u, hu, heq⟩
    refine ⟨u, hu, (translateSupport_injective a) ?_⟩
    change translateSupport T a = translateSupport (translateSupport S u) a
    rw [heq, translateSupport_add, translateSupport_add, add_comm a u]
  · rintro ⟨u, hu, heq⟩
    refine ⟨u, hu, ?_⟩
    rw [heq, translateSupport_add, translateSupport_add, add_comm a u]

/-- Exclusion of every translation is preserved under a common translation. -/
theorem anyTranslation_translate_iff (S T : Finset G) (a : G) :
    (∃ v : G, translateSupport T a = translateSupport (translateSupport S a) v) ↔
      (∃ v : G, T = translateSupport S v) := by
  constructor
  · rintro ⟨v, heq⟩
    refine ⟨v, (translateSupport_injective a) ?_⟩
    change translateSupport T a = translateSupport (translateSupport S v) a
    rw [heq, translateSupport_add, translateSupport_add, add_comm a v]
  · rintro ⟨v, heq⟩
    refine ⟨v, ?_⟩
    rw [heq, translateSupport_add, translateSupport_add, add_comm a v]

section Finite

variable [Fintype G]

theorem squareDeltaGraph_translate_iff (S T : Finset G) (a : G) (k : ℕ) :
    (squareDeltaGraph (G := G) k).Adj (translateSupport S a) (translateSupport T a) ↔
      (squareDeltaGraph (G := G) k).Adj S T := by
  simp only [squareDeltaGraph_adj_iff, translateSupport_card, ne_eq,
    translateSupport_eq_iff, orderedSquare_eq_translate_iff,
    translateSupport_symmDiff_card]

theorem ordinaryDeltaGraph_translate_iff (S T : Finset G) (a : G) (k : ℕ) :
    (ordinaryDeltaGraph (G := G) k).Adj (translateSupport S a) (translateSupport T a) ↔
      (ordinaryDeltaGraph (G := G) k).Adj S T := by
  simp only [ordinaryDeltaGraph, ordinaryGraph, translateSupport_card, ne_eq,
    translateSupport_eq_iff, ordinaryPartner_translate_iff,
    translateSupport_symmDiff_card]

theorem nontranslationDeltaGraph_translate_iff
    (S T : Finset G) (a : G) (k : ℕ) :
    (nontranslationDeltaGraph (G := G) k).Adj
        (translateSupport S a) (translateSupport T a) ↔
      (nontranslationDeltaGraph (G := G) k).Adj S T := by
  simp only [nontranslationDeltaGraph_adj_iff, translateSupport_card,
    orderedSquare_eq_translate_iff, anyTranslation_translate_iff,
    translateSupport_symmDiff_card]









/-- Uniform incidence transfer, including empty small-group cases. -/
theorem zeroFreeSquareDeltaPairCount_transfer (k : ℕ) :
    Fintype.card G * zeroFreeSquareDeltaPairCount (G := G) k =
      (Fintype.card G - (3 + k / 2)) * squareDeltaPairCount (G := G) k := by
  apply zeroFreeGraph_mul_edges (squareDeltaGraph (G := G) k) (3 + k / 2)
  · exact fun S T a => squareDeltaGraph_translate_iff S T a k
  · intro S T h
    obtain ⟨hS, hT, _, _, hk⟩ := (squareDeltaGraph_adj_iff S T k).mp h
    exact triple_union_card_of_symmDiff S T hS hT k hk



theorem zeroFreeOrdinaryDeltaPairCount_transfer (k : ℕ) :
    Fintype.card G * zeroFreeOrdinaryDeltaPairCount (G := G) k =
      (Fintype.card G - (3 + k / 2)) *
        (ordinaryDeltaGraph (G := G) k).edgeFinset.card := by
  apply zeroFreeGraph_mul_edges (ordinaryDeltaGraph (G := G) k) (3 + k / 2)
  · exact fun S T a => ordinaryDeltaGraph_translate_iff S T a k
  · rintro S T ⟨⟨hS, hT, _, _⟩, hk⟩
    exact triple_union_card_of_symmDiff S T hS hT k hk

theorem zeroFreeNontranslationDeltaPairCount_transfer (k : ℕ) :
    Fintype.card G * zeroFreeNontranslationDeltaPairCount (G := G) k =
      (Fintype.card G - (3 + k / 2)) *
        (nontranslationDeltaGraph (G := G) k).edgeFinset.card := by
  apply zeroFreeGraph_mul_edges (nontranslationDeltaGraph (G := G) k) (3 + k / 2)
  · exact fun S T a => nontranslationDeltaGraph_translate_iff S T a k
  · intro S T h
    obtain ⟨hS, hT, _, _, hk⟩ := (nontranslationDeltaGraph_adj_iff S T k).mp h
    exact triple_union_card_of_symmDiff S T hS hT k hk











/-- Weighted identity proving exact division by four. -/
theorem zeroFreeSquareDeltaPairCount_two_four_mul :
    4 * zeroFreeSquareDeltaPairCount (G := G) 2 =
      (Fintype.card G - 4) * (Fintype.card G - 2) *
        ((twoTorsion : Finset G).card - 1) := by
  have ht := zeroFreeSquareDeltaPairCount_transfer (G := G) 2
  norm_num at ht
  have hc := squareDeltaGraph_two_four_mul_edges (G := G)
  change 4 * squareDeltaPairCount (G := G) 2 = _ at hc
  have hc' : 4 * squareDeltaPairCount (G := G) 2 =
      Fintype.card G * ((Fintype.card G - 2) *
        ((twoTorsion : Finset G).card - 1)) := by simpa [Nat.mul_assoc] using hc
  simpa [Nat.mul_assoc] using zeroFreeDelta_cancel_formula
    (Fintype.card G) 4 4 _ _ _ Fintype.card_pos hc' ht

/-- Weighted identity proving exact division by two. -/
theorem zeroFreeSquareDeltaPairCount_four_two_mul :
    2 * zeroFreeSquareDeltaPairCount (G := G) 4 =
      (Fintype.card G - 5) * ((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1) := by
  have ht := zeroFreeSquareDeltaPairCount_transfer (G := G) 4
  norm_num at ht
  have hc := squareDeltaGraph_four_twice_edges_numeric (G := G)
  change 2 * squareDeltaPairCount (G := G) 4 = _ at hc
  have hc' : 2 * squareDeltaPairCount (G := G) 4 =
      Fintype.card G * (((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1)) := by simpa [Nat.mul_assoc] using hc
  simpa [Nat.mul_assoc] using zeroFreeDelta_cancel_formula
    (Fintype.card G) 5 2 _ _ _ Fintype.card_pos hc' ht

/-- The ordinary disjoint contribution, with exact division by twelve. -/
theorem zeroFreeOrdinaryDeltaPairCount_six_twelve_mul :
    12 * zeroFreeOrdinaryDeltaPairCount (G := G) 6 =
      (Fintype.card G - 6) * (Fintype.card G - 2) * (Fintype.card G - 4) *
        ((twoTorsion : Finset G).card - 1) := by
  have ht := zeroFreeOrdinaryDeltaPairCount_transfer (G := G) 6
  norm_num at ht
  have hc := ordinaryDeltaGraph_six_twelve_mul_edges (G := G)
  have hc' : 12 * (ordinaryDeltaGraph (G := G) 6).edgeFinset.card =
      Fintype.card G * ((Fintype.card G - 2) * (Fintype.card G - 4) *
        ((twoTorsion : Finset G).card - 1)) := by simpa [Nat.mul_assoc] using hc
  simpa [Nat.mul_assoc] using zeroFreeDelta_cancel_formula
    (Fintype.card G) 6 12 _ _ _ Fintype.card_pos hc' ht

/-- The exceptional disjoint contribution, with exact division by two. -/
theorem zeroFreeNontranslationDeltaPairCount_six_two_mul :
    2 * zeroFreeNontranslationDeltaPairCount (G := G) 6 =
      (Fintype.card G - 6) * ((twoTorsion : Finset G).card - 1) ^ 2 *
        ((threeTorsion : Finset G).card - 1) := by
  have ht := zeroFreeNontranslationDeltaPairCount_transfer (G := G) 6
  norm_num at ht
  have hc := nontranslationDeltaGraph_six_twice_edges_numeric (G := G)
  have hc' : 2 * (nontranslationDeltaGraph (G := G) 6).edgeFinset.card =
      Fintype.card G * (((twoTorsion : Finset G).card - 1) ^ 2 *
        ((threeTorsion : Finset G).card - 1)) := by simpa [Nat.mul_assoc] using hc
  simpa [Nat.mul_assoc] using zeroFreeDelta_cancel_formula
    (Fintype.card G) 6 2 _ _ _ Fintype.card_pos hc' ht



















/-- Each separate numerator is divisible by its stated denominator. -/
theorem p2m_local_zeroFreeSquareDeltaPairCount_divisibility :
    let n := Fintype.card G
    let h := (twoTorsion : Finset G).card
    let t := (threeTorsion : Finset G).card
    4 ∣ (n - 4) * (n - 2) * (h - 1) ∧
    2 ∣ (n - 5) * (h - 1) * (t - 1) ∧
    12 ∣ (n - 6) * (n - 2) * (n - 4) * (h - 1) ∧
    2 ∣ (n - 6) * (h - 1) ^ 2 * (t - 1) := by
  refine ⟨⟨_, (zeroFreeSquareDeltaPairCount_two_four_mul (G := G)).symm⟩,
    ⟨_, (zeroFreeSquareDeltaPairCount_four_two_mul (G := G)).symm⟩,
    ⟨_, (zeroFreeOrdinaryDeltaPairCount_six_twelve_mul (G := G)).symm⟩,
    ⟨_, (zeroFreeNontranslationDeltaPairCount_six_two_mul (G := G)).symm⟩⟩

end Finite

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  have n := @Fintype.card.{p2m_u_0} G inst_2;
  have h := @Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2);
  have t := @Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2);
  And
    (@Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) h
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
    (And
      (@Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) h
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) t
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (And
        (@Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) h
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) h
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) t
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeSquareDeltaPairCount_divisibility

