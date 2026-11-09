-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeCollisionDarts_delta_partition
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:51.165876+00:00
-- url     : https://prove2.me/submissions/1d3bd41c-afe6-488d-a635-5aab54af8b62

import Aesop
import Definitions.Def_Couret_Strobo2TorsFibreMoment_8377f9a18ab8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_triple_symmDiff_card_cases
import Definitions.Def_Couret_Strobo2TorsZeroFreeDeltaCount_41cbef917dd9
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Mathlib.Data.Sym.Card

set_option autoImplicit false

open scoped BigOperators symmDiff

/-!
M002.4: a combinatorial, rather than numerical, bridge between the second
binomial moment of the nonempty zero-free square fibres and the three
symmetric-difference collision edge counts.

The common object is an ordered pair of distinct supports in a single
restricted fibre. Each undirected graph edge has exactly two orientations.
No translation orbit is divided out, and no division of any numerical
closed-form count is used.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]



















/-- A true disjoint partition of all oriented collisions into the only
possible symmetric-difference cardinalities. -/
theorem p2m_local_zeroFreeCollisionDarts_delta_partition :
    (zeroFreeCollisionDarts (G := G)).card =
      ((zeroFreeCollisionDarts (G := G)).filter
        (fun p => (p.1 ∆ p.2).card = 2)).card +
      ((zeroFreeCollisionDarts (G := G)).filter
        (fun p => (p.1 ∆ p.2).card = 4)).card +
      ((zeroFreeCollisionDarts (G := G)).filter
        (fun p => (p.1 ∆ p.2).card = 6)).card := by
  classical
  let D := zeroFreeCollisionDarts (G := G)
  let A := D.filter (fun p => (p.1 ∆ p.2).card = 2)
  let B := D.filter (fun p => (p.1 ∆ p.2).card = 4)
  let C := D.filter (fun p => (p.1 ∆ p.2).card = 6)
  have hab : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpB
    have ha := (Finset.mem_filter.mp hpA).2
    have hb := (Finset.mem_filter.mp hpB).2
    omega
  have hac : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpC
    have ha := (Finset.mem_filter.mp hpA).2
    have hc := (Finset.mem_filter.mp hpC).2
    omega
  have hbc : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro p hpB hpC
    have hb := (Finset.mem_filter.mp hpB).2
    have hc := (Finset.mem_filter.mp hpC).2
    omega
  have habc : Disjoint (A ∪ B) C := by
    apply Finset.disjoint_left.mpr
    intro p hpAB hpC
    rcases Finset.mem_union.mp hpAB with hpA | hpB
    · exact (Finset.disjoint_left.mp hac) hpA hpC
    · exact (Finset.disjoint_left.mp hbc) hpB hpC
  have hunion : (A ∪ B) ∪ C = D := by
    ext p
    simp only [Finset.mem_union]
    constructor
    · rintro ((hpA | hpB) | hpC)
      · exact (Finset.mem_filter.mp hpA).1
      · exact (Finset.mem_filter.mp hpB).1
      · exact (Finset.mem_filter.mp hpC).1
    · intro hp
      have hd : p.1.card = 3 ∧ p.2.card = 3 ∧ p.1 ≠ p.2 ∧
          (∀ z : G, orderedSquare p.1 z = orderedSquare p.2 z) ∧
          0 ∉ p.1 ∧ 0 ∉ p.2 := (Finset.mem_filter.mp hp).2
      rcases triple_symmDiff_card_cases p.1 p.2 hd.1 hd.2.1 hd.2.2.1 with
        h2 | h4 | h6
      · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨hp, h2⟩))
      · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨hp, h4⟩))
      · exact Or.inr (Finset.mem_filter.mpr ⟨hp, h6⟩)
  change D.card = A.card + B.card + C.card
  calc
    D.card = ((A ∪ B) ∪ C).card := congrArg Finset.card hunion.symm
    _ = A.card + B.card + C.card := by
      rw [Finset.card_union_of_disjoint habc,
        Finset.card_union_of_disjoint hab]









end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.zeroFreeCollisionDarts.{p2m_u_0} G inst inst_1 inst_2))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
          (@Finset.filter.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
            (fun p =>
              @Eq.{1} Nat
                (@Finset.card.{p2m_u_0} G
                  (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                      (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G)
                        (@Finset.instLattice.{p2m_u_0} G inst_1)))
                    (@Finset.instSDiff.{p2m_u_0} G inst_1)
                    (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) p)
                    (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) p)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (fun a =>
              instDecidableEqNat
                (@Finset.card.{p2m_u_0} G
                  (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                      (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G)
                        (@Finset.instLattice.{p2m_u_0} G inst_1)))
                    (@Finset.instSDiff.{p2m_u_0} G inst_1)
                    (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) a)
                    (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) a)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Couret.STROBO2TORS.zeroFreeCollisionDarts.{p2m_u_0} G inst inst_1 inst_2)))
        (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
          (@Finset.filter.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
            (fun p =>
              @Eq.{1} Nat
                (@Finset.card.{p2m_u_0} G
                  (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                      (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G)
                        (@Finset.instLattice.{p2m_u_0} G inst_1)))
                    (@Finset.instSDiff.{p2m_u_0} G inst_1)
                    (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) p)
                    (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) p)))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun a =>
              instDecidableEqNat
                (@Finset.card.{p2m_u_0} G
                  (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                      (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G)
                        (@Finset.instLattice.{p2m_u_0} G inst_1)))
                    (@Finset.instSDiff.{p2m_u_0} G inst_1)
                    (@Prod.fst.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) a)
                    (@Prod.snd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G) a)))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@Couret.STROBO2TORS.zeroFreeCollisionDarts.{p2m_u_0} G inst inst_1 inst_2))))
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
          (@Couret.STROBO2TORS.zeroFreeCollisionDarts.{p2m_u_0} G inst inst_1 inst_2)))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeCollisionDarts_delta_partition

