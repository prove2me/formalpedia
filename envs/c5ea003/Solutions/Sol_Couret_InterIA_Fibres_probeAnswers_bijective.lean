-- Prove2me | solution 1 for Couret.InterIA.Fibres.probeAnswers_bijective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:38:34.604798+00:00
-- url     : https://prove2.me/submissions/795b2881-8c02-4580-99fd-64552cbb6fb7

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

theorem p2m_local_probeAnswers_bijective {α : Type*} [DecidableEq α] {d : ℕ}
    (P : Set (Finset α)) (q : Fin d → α) (hc : P.ncard=2^d) (hq : ProbeSeparates P q) :
    Function.Bijective (fun T : P => probeAnswers q T.val) := by
  classical
  have hnonzero : P.ncard ≠ 0 := by rw [hc]; exact pow_ne_zero _ (by omega)
  letI : Fintype P := (Set.finite_of_ncard_ne_zero hnonzero).fintype
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro T U he
    exact Subtype.ext (hq T.val T.property U.val U.property ((probeAnswers_eq_iff q _ _).mp he))
  · have he : Nat.card P=2^d := hc
    rw [Nat.card_eq_fintype_card] at he
    simpa using he







end Couret.InterIA.Fibres

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} α] {d : Nat} (P : Set.{p2m_u_0} (Finset.{p2m_u_0} α))
  (q : Fin d → α),
  @Eq.{1} Nat (@Set.ncard.{p2m_u_0} (Finset.{p2m_u_0} α) P)
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) d) →
    @Couret.InterIA.Fibres.ProbeSeparates.{p2m_u_0} α inst d P q →
      @Function.Bijective.{p2m_u_0 + 1, 1} (@Set.Elem.{p2m_u_0} (Finset.{p2m_u_0} α) P) (Fin d → Bool) fun T =>
        @Couret.InterIA.Fibres.probeAnswers.{p2m_u_0} α inst d q
          (@Subtype.val.{p2m_u_0 + 1} (Finset.{p2m_u_0} α)
            (fun x =>
              @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} α) (Set.{p2m_u_0} (Finset.{p2m_u_0} α))
                (@Set.instMembership.{p2m_u_0} (Finset.{p2m_u_0} α)) P x)
            T) := @_root_.Couret.InterIA.Fibres.p2m_local_probeAnswers_bijective

