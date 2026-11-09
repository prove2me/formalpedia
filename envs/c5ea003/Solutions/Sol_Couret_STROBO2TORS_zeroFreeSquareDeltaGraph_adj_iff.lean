-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeSquareDeltaGraph_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:58:18.541709+00:00
-- url     : https://prove2.me/submissions/569f47ce-7ae0-41a7-b0a7-17799e7b9c1d

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
import Theorems.Thm_Couret_STROBO2TORS_squareDeltaGraph_adj_iff
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





variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite

variable [Fintype G]













/-- The zero-free graph has exactly the intended adjacency. -/
theorem p2m_local_zeroFreeSquareDeltaGraph_adj_iff (S T : Finset G) (k : ℕ) :
    (zeroFreeGraph (squareDeltaGraph (G := G) k)).Adj S T ↔
      S.card = 3 ∧ T.card = 3 ∧ S ≠ T ∧
        (∀ z : G, orderedSquare S z = orderedSquare T z) ∧
        (S ∆ T).card = k ∧ 0 ∉ S ∧ 0 ∉ T := by
  change ((squareDeltaGraph (G := G) k).Adj S T ∧ 0 ∉ S ∧ 0 ∉ T) ↔ _
  rw [squareDeltaGraph_adj_iff]
  tauto















































end Finite

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S T : Finset.{p2m_u_0} G) (k : Nat),
  Iff
    (@SimpleGraph.Adj.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.zeroFreeGraph.{p2m_u_0} G inst
        (@Couret.STROBO2TORS.squareDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k))
      S T)
    (And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G T) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (And (@Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) S T)
          (And
            (∀ (z : G),
              @Eq.{1} Nat (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S z)
                (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 T z))
            (And
              (@Eq.{1} Nat
                (@Finset.card.{p2m_u_0} G
                  (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                      (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G)
                        (@Finset.instLattice.{p2m_u_0} G inst_1)))
                    (@Finset.instSDiff.{p2m_u_0} G inst_1) S T))
                k)
              (And
                (Not
                  (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G
                      (@Finset.instSetLike.{p2m_u_0} G))
                    S
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))))
                (Not
                  (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G
                      (@Finset.instSetLike.{p2m_u_0} G))
                    T
                    (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                      (@Zero.toOfNat0.{p2m_u_0} G
                        (@NegZeroClass.toZero.{p2m_u_0} G
                          (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                            (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                              (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                                (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))))))))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeSquareDeltaGraph_adj_iff

