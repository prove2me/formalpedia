-- Prove2me | solution 1 for Couret.STROBO2TORS.orderedNontranslationPairs_card_delta_partition
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:26.588195+00:00
-- url     : https://prove2.me/submissions/649c606a-4789-4c8d-acfa-f6f619c5c4bb

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
import Theorems.Thm_Couret_STROBO2TORS_NontranslationCollision_ne
import Theorems.Thm_Couret_STROBO2TORS_mem_orderedNontranslationPairs
import Theorems.Thm_Couret_STROBO2TORS_orderedSquare_symmDiff_two_iff
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_cases
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

/-- A historical zero-free nontranslation collision has delta four or six. -/
theorem NontranslationCollision.symmDiff_four_or_six {S T : Finset G}
    (h : NontranslationCollision S T) :
    (S ∆ T).card = 4 ∨ (S ∆ T).card = 6 := by
  rcases triple_symmDiff_card_cases S T h.1 h.2.1 h.ne with htwo | hfour | hsix
  · obtain ⟨u, _, hTu⟩ :=
      ((orderedSquare_symmDiff_two_iff S T h.1 h.2.1).mp
        ⟨h.2.2.2.2.1, htwo⟩).1
    exact (h.2.2.2.2.2 ⟨u, hTu⟩).elim
  · exact Or.inl hfour
  · exact Or.inr hsix

section Finite

variable [Fintype G]





/-- Exact disjoint subdivision of the ordered historical family. -/
theorem p2m_local_orderedNontranslationPairs_card_delta_partition :
    ((orderedNontranslationPairs : Finset (Finset G × Finset G)).filter
      (fun p => (p.1 ∆ p.2).card = 4)).card +
    ((orderedNontranslationPairs : Finset (Finset G × Finset G)).filter
      (fun p => (p.1 ∆ p.2).card = 6)).card =
      (orderedNontranslationPairs : Finset (Finset G × Finset G)).card := by
  classical
  let P := (orderedNontranslationPairs : Finset (Finset G × Finset G))
  let A := P.filter (fun p => (p.1 ∆ p.2).card = 4)
  let B := P.filter (fun p => (p.1 ∆ p.2).card = 6)
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p ha hb
    have ha4 := (Finset.mem_filter.mp ha).2
    have hb6 := (Finset.mem_filter.mp hb).2
    omega
  have hunion : A ∪ B = P := by
    ext p
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hp
      have hc := ((mem_orderedNontranslationPairs p.1 p.2).mp hp).symmDiff_four_or_six
      rcases hc with hfour | hsix
      · exact Or.inl ⟨hp, hfour⟩
      · exact Or.inr ⟨hp, hsix⟩
  change A.card + B.card = P.card
  rw [← Finset.card_union_of_disjoint hdisj, hunion]




end Finite

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
        (@Finset.filter.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
          (fun p =>
            @Eq.{1} Nat
              (@Finset.card.{p2m_u_0} G
                (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                  (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instLattice.{p2m_u_0} G inst_1)))
                  (@Finset.instSDiff.{p2m_u_0} G inst_1)
                  (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) p)
                  (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) p)))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (fun a =>
            instDecidableEqNat
              (@Finset.card.{p2m_u_0} G
                (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                  (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instLattice.{p2m_u_0} G inst_1)))
                  (@Finset.instSDiff.{p2m_u_0} G inst_1)
                  (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) a)
                  (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) a)))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@Couret.STROBO2TORS.orderedNontranslationPairs.{p2m_u_0} G inst inst_1 inst_2)))
      (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
        (@Finset.filter.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
          (fun p =>
            @Eq.{1} Nat
              (@Finset.card.{p2m_u_0} G
                (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                  (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instLattice.{p2m_u_0} G inst_1)))
                  (@Finset.instSDiff.{p2m_u_0} G inst_1)
                  (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) p)
                  (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) p)))
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (fun a =>
            instDecidableEqNat
              (@Finset.card.{p2m_u_0} G
                (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                  (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instLattice.{p2m_u_0} G inst_1)))
                  (@Finset.instSDiff.{p2m_u_0} G inst_1)
                  (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) a)
                  (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) a)))
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@Couret.STROBO2TORS.orderedNontranslationPairs.{p2m_u_0} G inst inst_1 inst_2))))
    (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.orderedNontranslationPairs.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_orderedNontranslationPairs_card_delta_partition

