-- Prove2me | solution 1 for Couret.InterIA.Fibres.MembershipTree.fixed_run
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:49.352777+00:00
-- url     : https://prove2.me/submissions/6b912c5f-eb63-422b-950b-993e43a2e6f4

import Definitions.Def_Couret_MembershipDecisionTree_ec39964080f5
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_FixedMembershipProbes_e6019f9e3a1b

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset



namespace MembershipTree





















theorem p2m_local_fixed_run {α : Type*} [DecidableEq α] (d : ℕ) (q : Fin d → α)
    (decode : (Fin d → Bool) → Finset α) (T : Finset α) :
    (fixed d q decode).run T=decode (probeAnswers q T) := by
  induction d with
  | zero =>
    change decode Fin.elim0=decode (probeAnswers q T)
    congr 1
    funext i
    exact Fin.elim0 i
  | succ d ih =>
    by_cases hx : q 0 ∈ T
    · simp only [fixed,run,if_pos hx]
      rw [ih]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [probeAnswers,hx]
      · simp [probeAnswers]
    · simp only [fixed,run,if_neg hx]
      rw [ih]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [probeAnswers,hx]
      · simp [probeAnswers]

end MembershipTree
end Couret.InterIA.Fibres

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} α] (d : Nat) (q : Fin d → α)
  (decode : (Fin d → Bool) → Finset.{p2m_u_0} α) (T : Finset.{p2m_u_0} α),
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} α)
    (@Couret.InterIA.Fibres.MembershipTree.run.{p2m_u_0} α inst
      (@Couret.InterIA.Fibres.MembershipTree.fixed.{p2m_u_0} α d q decode) T)
    (decode (@Couret.InterIA.Fibres.probeAnswers.{p2m_u_0} α inst d q T)) := @_root_.Couret.InterIA.Fibres.MembershipTree.p2m_local_fixed_run

