-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslationUnorderedPairCount_product
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:52:59.2602+00:00
-- url     : https://prove2.me/submissions/97353057-e715-4ef7-a600-8bcb12785c4d

import Aesop
import Definitions.Def_Couret_Strobo2TorsUnorderedPairs_09c78b93fb82
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_directed_nontranslation_degree_sum_numeric
import Theorems.Thm_Couret_STROBO2TORS_group_card_eq_h_mul_doublingImages
import Theorems.Thm_Couret_STROBO2TORS_nontranslationPairGraph_degree_sum
import Theorems.Thm_Couret_STROBO2TORS_threeTorsion_nonzero_card_eq_two_pairs
import Definitions.Def_Couret_Strobo2TorsNontranslationDegree_16ff2822736a
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

open scoped BigOperators

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



















/-- The handshaking identity, linked to the proved *directed* count.
This step is a real two-to-one statement about unordered pairs, not
a definition of "unordered" as one half of a numerical expression. -/
theorem nontranslationUnorderedPairCount_twice :
    2 * nontranslationUnorderedPairCount (G := G) =
      (Fintype.card G * ((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1)) *
        (twoTorsion : Finset G).card := by
  classical
  change 2 * (nontranslationPairGraph (G := G)).edgeFinset.card = _
  calc
    2 * (nontranslationPairGraph (G := G)).edgeFinset.card =
        (∑ S : Finset G, (nontranslationPairGraph (G := G)).degree S) :=
      (nontranslationPairGraph (G := G)).sum_degrees_eq_twice_card_edges.symm
    _ = ∑ S ∈ (tripleSupports : Finset (Finset G)),
          (nontranslatedNeighbours S).card :=
      nontranslationPairGraph_degree_sum
    _ = _ := directed_nontranslation_degree_sum_numeric

/-- Actual UNORDERED nontranslation-pair count, with quotient by swapping
proven by the graph handshake lemma.  The factors q and r are certified
existing quantities: q=|G/G[2]| and r=(|G[3]|-1)/2. -/
theorem p2m_local_nontranslationUnorderedPairCount_product :
    nontranslationUnorderedPairCount (G := G) =
      (doublingImages : Finset G).card *
        (twoTorsion : Finset G).card *
        (twoTorsion : Finset G).card *
        ((twoTorsion : Finset G).card - 1) *
        (threeSignPairs : Finset (Finset G)).card := by
  have hDouble := nontranslationUnorderedPairCount_twice (G := G)
  rw [group_card_eq_h_mul_doublingImages,
    threeTorsion_nonzero_card_eq_two_pairs] at hDouble
  have hTwice :
      2 * nontranslationUnorderedPairCount (G := G) =
        2 * ((doublingImages : Finset G).card *
          (twoTorsion : Finset G).card *
          (twoTorsion : Finset G).card *
          ((twoTorsion : Finset G).card - 1) *
          (threeSignPairs : Finset (Finset G)).card) := by
    calc
      2 * nontranslationUnorderedPairCount (G := G) =
        ((twoTorsion : Finset G).card * (doublingImages : Finset G).card *
          ((twoTorsion : Finset G).card - 1) *
          (2 * (threeSignPairs : Finset (Finset G)).card)) *
          (twoTorsion : Finset G).card := hDouble
      _ = _ := by ring
  omega

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat (@Couret.STROBO2TORS.nontranslationUnorderedPairCount.{p2m_u_0} G inst inst_1 inst_2)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.doublingImages.{p2m_u_0} G inst inst_1 inst_2))
            (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G) (@Couret.STROBO2TORS.threeSignPairs.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslationUnorderedPairCount_product

