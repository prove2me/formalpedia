-- Prove2me | solution 1 for Couret.STROBO2TORS.squareDeltaPairCount_numeric
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:46.779358+00:00
-- url     : https://prove2.me/submissions/9c2b68f1-eeea-4ff7-8b60-d462742509fa

import Aesop
import Definitions.Def_Couret_Strobo2TorsDeltaCount_79a5ff554435
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Theorems.Thm_Couret_STROBO2TORS_nontranslationDeltaGraph_six_twice_edges_numeric
import Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_six_twelve_mul_edges
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_edges_partition
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_four_twice_edges_numeric
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_two_four_mul_edges
import Definitions.Def_Couret_Strobo2TorsDeltaTwoCount_96c8f007ba6a
import Definitions.Def_Couret_Strobo2TorsDeltaExceptionalCount_9f9783d90924
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
Exact unordered pair counts at symmetric-difference sizes two, four and six.
The vertices are three-element subsets of a finite abelian group; zero is
permitted. The graph adjacency theorem identifies the counted objects with
the labelled ordered convolution square, including diagonal pairs.
The two branch graphs have disjoint neighbour sets, so their edge counts
add. Natural-number subtraction is used throughout, including small groups.
-/

namespace Couret.STROBO2TORS





variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]















theorem ordinaryDeltaGraph_six_edges_numeric :
    (ordinaryDeltaGraph (G := G) 6).edgeFinset.card =
      Fintype.card G * (Fintype.card G - 2) * (Fintype.card G - 4) *
        ((twoTorsion : Finset G).card - 1) / 12 := by
  have h := ordinaryDeltaGraph_six_twelve_mul_edges (G := G)
  omega









theorem squareDeltaPairCount_two :
    squareDeltaPairCount (G := G) 2 =
      Fintype.card G * (Fintype.card G - 2) *
        ((twoTorsion : Finset G).card - 1) / 4 := by
  have h := squareDeltaGraph_two_four_mul_edges (G := G)
  unfold squareDeltaPairCount
  omega

theorem squareDeltaPairCount_four :
    squareDeltaPairCount (G := G) 4 =
      Fintype.card G * ((twoTorsion : Finset G).card - 1) *
        ((threeTorsion : Finset G).card - 1) / 2 := by
  have h := squareDeltaGraph_four_twice_edges_numeric (G := G)
  unfold squareDeltaPairCount
  omega

theorem squareDeltaPairCount_six :
    squareDeltaPairCount (G := G) 6 =
      Fintype.card G * (Fintype.card G - 2) * (Fintype.card G - 4) *
        ((twoTorsion : Finset G).card - 1) / 12 +
      Fintype.card G * ((twoTorsion : Finset G).card - 1) ^ 2 *
        ((threeTorsion : Finset G).card - 1) / 2 := by
  unfold squareDeltaPairCount
  rw [squareDeltaGraph_edges_partition, ordinaryDeltaGraph_six_edges_numeric]
  have he := nontranslationDeltaGraph_six_twice_edges_numeric (G := G)
  have hCount :
      (nontranslationDeltaGraph (G := G) 6).edgeFinset.card =
        Fintype.card G * ((twoTorsion : Finset G).card - 1) ^ 2 *
          ((threeTorsion : Finset G).card - 1) / 2 := by omega
  rw [hCount]

/-- The complete numerical delta subdivision, with zero permitted in supports. -/
theorem p2m_local_squareDeltaPairCount_numeric :
    let n := Fintype.card G
    let h := (twoTorsion : Finset G).card
    let t := (threeTorsion : Finset G).card
    squareDeltaPairCount (G := G) 2 = n * (n - 2) * (h - 1) / 4 ∧
    squareDeltaPairCount (G := G) 4 = n * (h - 1) * (t - 1) / 2 ∧
    squareDeltaPairCount (G := G) 6 =
      n * (n - 2) * (n - 4) * (h - 1) / 12 +
        n * (h - 1) ^ 2 * (t - 1) / 2 := by
  exact ⟨squareDeltaPairCount_two, squareDeltaPairCount_four, squareDeltaPairCount_six⟩


end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  have n := @Fintype.card.{p2m_u_0} G inst_2;
  have h := @Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2);
  have t := @Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.threeTorsion.{p2m_u_0} G inst inst_1 inst_2);
  And
    (@Eq.{1} Nat
      (@Couret.STROBO2TORS.squareDeltaPairCount.{p2m_u_0} G inst inst_1 inst_2
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) h
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    (And
      (@Eq.{1} Nat
        (@Couret.STROBO2TORS.squareDeltaPairCount.{p2m_u_0} G inst inst_1 inst_2
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) h
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) t
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@Eq.{1} Nat
        (@Couret.STROBO2TORS.squareDeltaPairCount.{p2m_u_0} G inst inst_1 inst_2
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) h
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) n
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) h
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) t
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) := @_root_.Couret.STROBO2TORS.p2m_local_squareDeltaPairCount_numeric

