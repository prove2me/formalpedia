-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeNontranslationDeltaPairCount_four_add_six
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:58:38.540187+00:00
-- url     : https://prove2.me/submissions/ac001f23-fa71-4643-bb1d-804b486e1d9b

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Definitions.Def_Couret_Strobo2TorsZeroFreeDeltaCount_41cbef917dd9
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_mem_orderedNontranslationPairs
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_adj_iff
import Theorems.Thm_Couret_STROBO2TORS_orderedNontranslationPairs_card_delta_partition
import Theorems.Thm_Couret_STROBO2TORS_orderedNontranslationPairs_card_eq_twice
import Definitions.Def_Couret_Strobo2TorsZeroFreeDeltaCount_41cbef917dd9
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact compatibility with the historical zero-free nontranslation-pair count.
This identifies the counted objects, not merely their numerical formulas:
the old family is the disjoint union of the new delta-four and delta-six
families. All historical definitions and proofs are retained unchanged.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



section Finite

variable [Fintype G]

/-- The new restricted adjacency is the old collision predicate with delta fixed. -/
theorem zeroFreeNontranslationDeltaGraph_adj_iff (S T : Finset G) (k : ℕ) :
    (zeroFreeGraph (nontranslationDeltaGraph (G := G) k)).Adj S T ↔
      NontranslationCollision S T ∧ (S ∆ T).card = k := by
  change ((nontranslationDeltaGraph (G := G) k).Adj S T ∧ 0 ∉ S ∧ 0 ∉ T) ↔ _
  rw [nontranslationDeltaGraph_adj_iff]
  unfold NontranslationCollision
  tauto

/-- The twice-counted new edges are exactly the ordered historical pairs
at that delta; orientation has the same convention in both libraries. -/
theorem zeroFreeNontranslationDeltaPairCount_twice_eq_filtered (k : ℕ) :
    2 * zeroFreeNontranslationDeltaPairCount (G := G) k =
      ((orderedNontranslationPairs : Finset (Finset G × Finset G)).filter
        (fun p => (p.1 ∆ p.2).card = k)).card := by
  classical
  unfold zeroFreeNontranslationDeltaPairCount
  rw [SimpleGraph.two_mul_card_edgeFinset]
  congr 1
  ext ⟨S, T⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    zeroFreeNontranslationDeltaGraph_adj_iff, mem_orderedNontranslationPairs]



/-- The two new exceptional counts sum to the exact historical count of
unordered zero-free nontranslation pairs, for every finite abelian group. -/
theorem p2m_local_zeroFreeNontranslationDeltaPairCount_four_add_six :
    zeroFreeNontranslationDeltaPairCount (G := G) 4 +
      zeroFreeNontranslationDeltaPairCount (G := G) 6 =
      (nontranslationPairs : Finset (Finset (Finset G))).card := by
  have h := orderedNontranslationPairs_card_delta_partition (G := G)
  rw [← zeroFreeNontranslationDeltaPairCount_twice_eq_filtered,
    ← zeroFreeNontranslationDeltaPairCount_twice_eq_filtered,
    orderedNontranslationPairs_card_eq_twice] at h
  omega


end Finite

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Couret.STROBO2TORS.zeroFreeNontranslationDeltaPairCount.{p2m_u_0} G inst inst_1 inst_2
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@Couret.STROBO2TORS.zeroFreeNontranslationDeltaPairCount.{p2m_u_0} G inst inst_1 inst_2
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.nontranslationPairs.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeNontranslationDeltaPairCount_four_add_six

