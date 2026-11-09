-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_anchored_dedup_mem_source
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:02:01.039208+00:00
-- url     : https://prove2.me/submissions/092cec38-79b4-4599-a4b5-0f96588cce24

import Aesop
import Definitions.Def_Couret_RecohCompactOrbitBridge_59017063a1ce
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a

set_option autoImplicit false

/-!
An anchored orbit test and a finite-list deduplication invariant.

The orbit test fixes one point of the left support and examines only the
points of the right support. It therefore examines three differences when
the right support has cardinal three. No ambient-group search is used.

The list routine retains the last representative of each orbit. This is a
deliberate model at the quotient level, not an assertion that its order or
chosen representatives equal the Python routine's first-retention order.
The results below concern represented orbits and pairwise inequivalence.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]















theorem p2m_local_recoh_anchored_dedup_mem_source (anchor : Finset G → G)
    (xs : List (Finset G)) (B : Finset G)
    (hB : B ∈ recohAnchoredOrbitDedup anchor xs) : B ∈ xs := by
  induction xs with
  | nil => simp [recohAnchoredOrbitDedup] at hB
  | cons C xs ih =>
    simp only [recohAnchoredOrbitDedup] at hB
    split_ifs at hB with hseen
    · exact List.mem_cons_of_mem C (ih hB)
    · rcases List.mem_cons.mp hB with rfl | hB
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem C (ih hB)











section Finite

variable [Fintype G]





end Finite

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (anchor : Finset.{p2m_u_0} G → G) (xs : List.{p2m_u_0} (Finset.{p2m_u_0} G)) (B : Finset.{p2m_u_0} G),
  @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (List.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@List.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.recohAnchoredOrbitDedup.{p2m_u_0} G inst inst_1 anchor xs) B →
    @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (List.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@List.instMembership.{p2m_u_0} (Finset.{p2m_u_0} G)) xs B := @_root_.Couret.STROBO2TORS.p2m_local_recoh_anchored_dedup_mem_source

