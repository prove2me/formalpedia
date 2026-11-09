-- Prove2me | solution 1 for Couret.STROBO2TORS.ordinaryDeltaGraph_six_twelve_mul_edges
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:45.839555+00:00
-- url     : https://prove2.me/submissions/80b1171f-2be4-4774-9915-f5c91221dbe9

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
import Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_two_four_mul_edges
import Theorems.Thm_Couret_STROBO2TORS_ordinaryDeltaGraph_two_six_twice_edges
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

private theorem deltaCount_choose_three_balance (n : ℕ) :
    6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  have h := (Nat.descFactorial_eq_factorial_mul_choose n 3).symm
  norm_num [Nat.factorial, Nat.descFactorial] at h
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

private theorem deltaCount_six_from_balance (n r a b : ℕ)
    (hsum : 2 * (a + b) = n.choose 3 * r)
    (htwo : 4 * a = n * (n - 2) * r) :
    12 * b = n * (n - 2) * (n - 4) * r := by
  by_cases hn : 4 ≤ n
  · have hsum6 : 12 * a + 12 * b = n * (n - 1) * (n - 2) * r := by
      calc
        12 * a + 12 * b = 6 * (2 * (a + b)) := by ring
        _ = 6 * (n.choose 3 * r) := by rw [hsum]
        _ = (6 * n.choose 3) * r := by ring
        _ = n * (n - 1) * (n - 2) * r := by
          rw [deltaCount_choose_three_balance]
    have hsub : n - 1 = 3 + (n - 4) := by omega
    have hprod : n * (n - 1) * (n - 2) * r =
        3 * (n * (n - 2) * r) + n * (n - 2) * (n - 4) * r := by
      rw [hsub]
      ring
    have ha : 12 * a = 3 * (n * (n - 2) * r) := by
      calc
        12 * a = 3 * (4 * a) := by ring
        _ = 3 * (n * (n - 2) * r) := by rw [htwo]
    rw [hprod, ha] at hsum6
    omega
  · have hnSmall : n ≤ 3 := by omega
    interval_cases n <;> norm_num [Nat.choose] at hsum htwo ⊢ <;> omega

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]













/-- Twelve times the ordinary delta-six count, including small-group cases. -/
theorem p2m_local_ordinaryDeltaGraph_six_twelve_mul_edges :
    12 * (ordinaryDeltaGraph (G := G) 6).edgeFinset.card =
      Fintype.card G * (Fintype.card G - 2) * (Fintype.card G - 4) *
        ((twoTorsion : Finset G).card - 1) := by
  exact deltaCount_six_from_balance (Fintype.card G)
    ((twoTorsion : Finset G).card - 1)
    (ordinaryDeltaGraph (G := G) 2).edgeFinset.card
    (ordinaryDeltaGraph (G := G) 6).edgeFinset.card
    ordinaryDeltaGraph_two_six_twice_edges ordinaryDeltaGraph_two_four_mul_edges




















end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
      (@Finset.card.{p2m_u_0} (Sym2.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@SimpleGraph.edgeFinset.{p2m_u_0} (Finset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@SimpleGraph.fintypeEdgeSet.{p2m_u_0} (Finset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.ordinaryDeltaGraph.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@Sym2.instFintype.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.fintype.{p2m_u_0} G inst_2))
            (@Couret.STROBO2TORS.ordinaryDeltaGraph_decidableRel.{p2m_u_0} G inst inst_1 inst_2
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Fintype.card.{p2m_u_0} G inst_2)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Fintype.card.{p2m_u_0} G inst_2)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Fintype.card.{p2m_u_0} G inst_2)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
        (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_ordinaryDeltaGraph_six_twelve_mul_edges

