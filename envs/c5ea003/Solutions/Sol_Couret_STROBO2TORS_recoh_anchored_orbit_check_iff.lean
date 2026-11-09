-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_anchored_orbit_check_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:02:10.306804+00:00
-- url     : https://prove2.me/submissions/2e0ef6a2-bec3-4524-8274-c1dc17f7c988

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



theorem p2m_local_recoh_anchored_orbit_check_iff (b₀ : G) (B C : Finset G)
    (hb₀ : b₀ ∈ B) :
    recohAnchoredOrbitCheck b₀ B C = true ↔ OrdinaryPartner B C := by
  simp only [recohAnchoredOrbitCheck, decide_eq_true_eq]
  constructor
  · rintro ⟨c, _, hu, hC⟩
    exact ⟨c - b₀, hu, hC⟩
  · rintro ⟨u, hu, hC⟩
    have hpoint : b₀ + u ∈ C := by
      rw [hC]
      exact Finset.mem_image.mpr ⟨b₀, hb₀, rfl⟩
    refine ⟨b₀ + u, hpoint, ?_, ?_⟩
    · simpa only [add_sub_cancel_left] using hu
    · simpa only [add_sub_cancel_left] using hC























section Finite

variable [Fintype G]





end Finite

end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (b₀ : G)
  (B C : Finset.{p2m_u_0} G),
  @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) B b₀ →
    Iff (@Eq.{1} Bool (@Couret.STROBO2TORS.recohAnchoredOrbitCheck.{p2m_u_0} G inst inst_1 b₀ B C) Bool.true)
      (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 B C) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_anchored_orbit_check_iff

