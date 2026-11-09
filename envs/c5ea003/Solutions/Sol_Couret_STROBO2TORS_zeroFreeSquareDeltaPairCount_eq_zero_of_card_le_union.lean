-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeSquareDeltaPairCount_eq_zero_of_card_le_union
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:59:46.106196+00:00
-- url     : https://prove2.me/submissions/03b0e9b4-5271-45b1-8f8d-788b5fae0831

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
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_eq_translate_iff
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_adj_iff
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





section Finite

variable [Fintype G]

theorem squareDeltaGraph_translate_iff (S T : Finset G) (a : G) (k : ℕ) :
    (squareDeltaGraph (G := G) k).Adj (translateSupport S a) (translateSupport T a) ↔
      (squareDeltaGraph (G := G) k).Adj S T := by
  simp only [squareDeltaGraph_adj_iff, translateSupport_card, ne_eq,
    translateSupport_eq_iff, orderedSquare_eq_translate_iff,
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









/-- There is no zero-free pair when its union would occupy the entire group. -/
theorem p2m_local_zeroFreeSquareDeltaPairCount_eq_zero_of_card_le_union (k : ℕ)
    (hn : Fintype.card G ≤ 3 + k / 2) :
    zeroFreeSquareDeltaPairCount (G := G) k = 0 := by
  apply Nat.eq_of_mul_eq_mul_left (Fintype.card_pos (α := G))
  simpa [Nat.sub_eq_zero_of_le hn] using
    zeroFreeSquareDeltaPairCount_transfer (G := G) k



































end Finite

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (k : Nat),
  @LE.le.{0} Nat instLENat (@Fintype.card.{p2m_u_0} G inst_2)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    @Eq.{1} Nat (@Couret.STROBO2TORS.zeroFreeSquareDeltaPairCount.{p2m_u_0} G inst inst_1 inst_2 k)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeSquareDeltaPairCount_eq_zero_of_card_le_union

