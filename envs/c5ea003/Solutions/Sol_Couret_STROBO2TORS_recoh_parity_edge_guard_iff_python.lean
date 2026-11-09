-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_parity_edge_guard_iff_python
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:55:58.529596+00:00
-- url     : https://prove2.me/submissions/fcb766a8-4fee-4667-936d-4fd7bc871e7d

import Aesop
import Definitions.Def_Couret_RecohParityGuardBridge_a0468e3b1d7b
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
import Definitions.Def_Couret_RecohParityGenerator_deb90a4bb68d

set_option autoImplicit false

/-!
Exact arithmetic correspondence between the Lean residual guards and the
subtraction, parity and indicator-value guards in Python v0.2.

This proves equal mathematical predicates. It is not a formal semantics of
Python integer operations, parsing, exceptions or serialization.
-/

namespace Couret.STROBO2TORS



theorem recoh_residual_indicator_iff (n i : ℕ) :
    n = i + 2 * (if 0 < (n - i) / 2 then 1 else 0) ↔
      recohPythonResidualGuard n i := by
  unfold recohPythonResidualGuard
  by_cases h : 0 < (n - i) / 2
  · simp only [if_pos h]
    omega
  · simp only [if_neg h]
    omega

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [AddCommGroup G] in
theorem p2m_local_recoh_parity_edge_guard_iff_python (U : Finset G) (R : G → ℕ) :
    recohParityEdgeGuard U R ↔
      ∀ z ∈ U, recohPythonResidualGuard (R z)
        (recohParityIndicator (recohParityOddSupport U R) z) := by
  unfold recohParityEdgeGuard
  apply forall_congr'
  intro z
  apply forall_congr'
  intro hz
  have hmem : z ∈ recohParityEdges U R ↔
      0 < (R z - recohParityIndicator (recohParityOddSupport U R) z) / 2 := by
    simp only [recohParityEdges, Finset.mem_filter, recohParityEdgeResidual,
      hz, true_and]
  have hindicator : recohParityIndicator (recohParityEdges U R) z =
      (if 0 < (R z - recohParityIndicator (recohParityOddSupport U R) z) / 2
       then 1 else 0) := by
    change (if z ∈ recohParityEdges U R then 1 else 0) = _
    by_cases h : 0 < (R z - recohParityIndicator (recohParityOddSupport U R) z) / 2
    · rw [if_pos (hmem.mpr h), if_pos h]
    · rw [if_neg (fun hz' => h (hmem.mp hz')), if_neg h]
  rw [hindicator]
  exact recoh_residual_indicator_iff (R z)
    (recohParityIndicator (recohParityOddSupport U R) z)



end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} G] (U : Finset.{p2m_u_0} G) (R : G → Nat),
  Iff (@Couret.STROBO2TORS.recohParityEdgeGuard.{p2m_u_0} G inst U R)
    (∀ (z : G),
      @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) U z →
        Couret.STROBO2TORS.recohPythonResidualGuard (R z)
          (@Couret.STROBO2TORS.recohParityIndicator.{p2m_u_0} G inst
            (@Couret.STROBO2TORS.recohParityOddSupport.{p2m_u_0} G U R) z)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_parity_edge_guard_iff_python

