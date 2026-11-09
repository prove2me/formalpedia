-- Prove2me | solution 1 for Couret.InterIA.Fibres.probeDecode_correct
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:08.647105+00:00
-- url     : https://prove2.me/submissions/8c6d69de-bb45-4ed7-a6ed-38f2e7634a54

import Definitions.Def_Couret_FixedMembershipProbes_e6019f9e3a1b
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
import Definitions.Def_Couret_BinaryAffineFibre_5ba9c7ff8364
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity



















theorem probeAnswers_eq_iff {α : Type*} [DecidableEq α] {d : ℕ}
    (q : Fin d → α) (T U : Finset α) :
    probeAnswers q T=probeAnswers q U ↔ ∀ i, q i ∈ T ↔ q i ∈ U := by
  simp only [funext_iff,probeAnswers,decide_eq_decide]





theorem p2m_local_probeDecode_correct {α : Type*} [DecidableEq α] {d : ℕ}
    (P : Set (Finset α)) (q : Fin d → α) (fallback : Finset α) (hq : ProbeSeparates P q)
    (T : Finset α) (hT : T ∈ P) : probeDecode P q fallback (probeAnswers q T)=T := by
  classical
  have he : ∃ U ∈ P, probeAnswers q U=probeAnswers q T := ⟨T,hT,rfl⟩
  unfold probeDecode
  rw [dif_pos he]
  exact hq _ (Classical.choose_spec he).1 T hT
    ((probeAnswers_eq_iff q _ T).mp (Classical.choose_spec he).2)



end Couret.InterIA.Fibres

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} α] {d : Nat} (P : Set.{p2m_u_0} (Finset.{p2m_u_0} α))
  (q : Fin d → α) (fallback : Finset.{p2m_u_0} α),
  @Couret.InterIA.Fibres.ProbeSeparates.{p2m_u_0} α inst d P q →
    ∀ (T : Finset.{p2m_u_0} α),
      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} α) (Set.{p2m_u_0} (Finset.{p2m_u_0} α))
          (@Set.instMembership.{p2m_u_0} (Finset.{p2m_u_0} α)) P T →
        @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} α)
          (@Couret.InterIA.Fibres.probeDecode.{p2m_u_0} α inst d P q fallback
            (@Couret.InterIA.Fibres.probeAnswers.{p2m_u_0} α inst d q T))
          T := @_root_.Couret.InterIA.Fibres.p2m_local_probeDecode_correct

