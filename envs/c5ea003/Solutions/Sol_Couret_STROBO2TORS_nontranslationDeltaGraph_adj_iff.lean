-- Prove2me | solution 1 for Couret.STROBO2TORS.nontranslationDeltaGraph_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:42.690416+00:00
-- url     : https://prove2.me/submissions/75fce3e4-bbb4-4901-99aa-feed6a826f1b

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



theorem mem_nontranslationDeltaNeighbours (S T : Finset G) (k : ℕ)
    (hS : S.card = 3) :
    T ∈ nontranslationDeltaNeighbours S k ↔
      T.card = 3 ∧ (∀ z : G, orderedSquare S z = orderedSquare T z) ∧
        (¬ ∃ v : G, T = translateSupport S v) ∧ (S ∆ T).card = k := by
  rw [nontranslationDeltaNeighbours, Finset.mem_filter,
    mem_nontranslatedNeighbours S T hS]
  tauto





theorem p2m_local_nontranslationDeltaGraph_adj_iff (S T : Finset G) (k : ℕ) :
    (nontranslationDeltaGraph (G := G) k).Adj S T ↔
      S.card = 3 ∧ T.card = 3 ∧
        (∀ z : G, orderedSquare S z = orderedSquare T z) ∧
        (¬ ∃ v : G, T = translateSupport S v) ∧ (S ∆ T).card = k := by
  change (S.card = 3 ∧ T ∈ nontranslationDeltaNeighbours S k) ↔ _
  constructor
  · rintro ⟨hS, hT⟩
    exact ⟨hS, (mem_nontranslationDeltaNeighbours S T k hS).mp hT⟩
  · rintro ⟨hS, hT⟩
    exact ⟨hS, (mem_nontranslationDeltaNeighbours S T k hS).mpr hT⟩
































end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S T : Finset.{p2m_u_0} G) (k : Nat),
  Iff
    (@SimpleGraph.Adj.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.nontranslationDeltaGraph.{p2m_u_0} G inst inst_1 inst_2 k) S T)
    (And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G T) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (And
          (∀ (z : G),
            @Eq.{1} Nat (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S z)
              (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 T z))
          (And
            (Not
              (@Exists.{p2m_u_0 + 1} G fun v =>
                @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) T
                  (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S v)))
            (@Eq.{1} Nat
              (@Finset.card.{p2m_u_0} G
                (@symmDiff.{p2m_u_0} (Finset.{p2m_u_0} G)
                  (@SemilatticeSup.toMax.{p2m_u_0} (Finset.{p2m_u_0} G)
                    (@Lattice.toSemilatticeSup.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instLattice.{p2m_u_0} G inst_1)))
                  (@Finset.instSDiff.{p2m_u_0} G inst_1) S T))
              k))))) := @_root_.Couret.STROBO2TORS.p2m_local_nontranslationDeltaGraph_adj_iff

