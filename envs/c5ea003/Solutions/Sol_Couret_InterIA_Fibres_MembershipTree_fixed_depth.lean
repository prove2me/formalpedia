-- Prove2me | solution 1 for Couret.InterIA.Fibres.MembershipTree.fixed_depth
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:28.695931+00:00
-- url     : https://prove2.me/submissions/a17e1261-33d4-484e-af21-fc8779ac715f

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



















theorem p2m_local_fixed_depth {α : Type*} (d : ℕ) (q : Fin d → α) (decode : (Fin d → Bool) → Finset α) :
    (fixed d q decode).depth=d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [fixed,depth,ih,Nat.max_self]



end MembershipTree
end Couret.InterIA.Fibres

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} (d : Nat) (q : Fin d → α) (decode : (Fin d → Bool) → Finset.{p2m_u_0} α),
  @Eq.{1} Nat
    (@Couret.InterIA.Fibres.MembershipTree.depth.{p2m_u_0} α
      (@Couret.InterIA.Fibres.MembershipTree.fixed.{p2m_u_0} α d q decode))
    d := @_root_.Couret.InterIA.Fibres.MembershipTree.p2m_local_fixed_depth

