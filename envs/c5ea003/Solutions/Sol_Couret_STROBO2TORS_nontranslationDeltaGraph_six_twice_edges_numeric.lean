-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslationDeltaGraph_six_twice_edges_numeric
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:17.57868+00:00
-- url     : https://prove2.me/submissions/404dc464-48f1-4812-ad70-a0b53c4b2097

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaExceptionalCount_9f9783d90924
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_degree_six
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Definitions.Def_Couret_Strobo2TorsNontranslationUnordered_7692bff20374

set_option autoImplicit false

/-!
Unordered nontranslation collisions, split by symmetric-difference size.
The ambient group is finite abelian, supports have cardinality three, and
zero is permitted. An exceptional source has one delta-four neighbour and
`|G[2]| - 1` delta-six neighbours. Graph degree sums count unordered pairs
twice, so the final statements require no division in natural numbers.
-/

open scoped BigOperators symmDiff

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]































private theorem deltaCount_twice_edges_of_degree (k c : ℕ)
    (hdegree : ∀ S : Finset G,
      (nontranslationDeltaGraph (G := G) k).degree S =
        if S ∈ (exceptionalSupports : Finset (Finset G)) then c else 0) :
    2 * (nontranslationDeltaGraph (G := G) k).edgeFinset.card =
      (exceptionalSupports : Finset (Finset G)).card * c := by
  classical
  have hFilter : (Finset.univ : Finset (Finset G)).filter
      (fun S => S ∈ (exceptionalSupports : Finset (Finset G))) = exceptionalSupports := by
    ext S
    simp
  calc
    2 * (nontranslationDeltaGraph (G := G) k).edgeFinset.card =
        ∑ S : Finset G, (nontranslationDeltaGraph (G := G) k).degree S :=
      (nontranslationDeltaGraph (G := G) k).sum_degrees_eq_twice_card_edges.symm
    _ = ∑ S : Finset G,
        (if S ∈ (exceptionalSupports : Finset (Finset G)) then c else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      exact hdegree S
    _ = ∑ S ∈ ((Finset.univ : Finset (Finset G)).filter
        (fun S => S ∈ (exceptionalSupports : Finset (Finset G)))), c := by
      rw [Finset.sum_filter]
    _ = (exceptionalSupports : Finset (Finset G)).card * c := by
      rw [hFilter]
      simp





/-- The unordered exceptional delta-six count, multiplied by two. -/
theorem nontranslationDeltaGraph_six_twice_edges :
    2 * (nontranslationDeltaGraph (G := G) 6).edgeFinset.card =
      (exceptionalSupports : Finset (Finset G)).card *
        ((twoTorsion : Finset G).card - 1) := by
  exact deltaCount_twice_edges_of_degree (G := G) 6
    ((twoTorsion : Finset G).card - 1) nontranslationDeltaGraph_degree_six

/-- Twice the number of unordered exceptional delta-six pairs is
n(h-1)^2(t-1), with zero permitted in the supports. -/
theorem p2m_local_nontranslationDeltaGraph_six_twice_edges_numeric :
    2 * (nontranslationDeltaGraph (G := G) 6).edgeFinset.card =
      Fintype.card G * ((twoTorsion : Finset G).card - 1) ^ 2 *
        ((threeTorsion : Finset G).card - 1) := by
  rw [nontranslationDeltaGraph_six_twice_edges, exceptionalSupports_card]
  simp only [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]


end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.nontranslationDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.nontranslationDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
            (@Couret.STROBO2TORS.nontranslationDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslationDeltaGraph_six_twice_edges_numeric

