-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.sevenDistinct_reindex
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:07:13.782963+00:00
-- url     : https://prove2.me/submissions/a5a487a3-af41-4e37-934c-87537054dd4a

import Definitions.Def_Couret_RelabelBasics_a474d20b9d5f
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_distinctLabels_of_injective_nonzero
import Theorems.Thm_Couret_InterIA_SingletonNecessity_nonzero_of_distinctLabels
import Theorems.Thm_Couret_InterIA_SingletonNecessity_sevenDistinct_injective
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset
variable {G : Type*} [AddCommGroup G] [DecidableEq G]



theorem p2m_local_sevenDistinct_reindex (x : Fin 6 → G) (hd : SevenDistinct x)
    (p : Fin 6 → Fin 6) (hp : Function.Injective p) : SevenDistinct (reindex x p) := by
  apply distinctLabels_of_injective_nonzero
  · exact (sevenDistinct_injective x hd).comp hp
  · intro i
    exact nonzero_of_distinctLabels x hd (p i)









end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [DecidableEq.{p2m_u_0 + 1} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
  @Couret.InterIA.SingletonNecessity.SevenDistinct.{p2m_u_0} G inst x →
    ∀
      (p :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) →
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))),
      @Function.Injective.{1, 1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) p →
        @Couret.InterIA.SingletonNecessity.SevenDistinct.{p2m_u_0} G inst
          (@Couret.InterIA.SingletonNecessity.reindex.{p2m_u_0} G x p) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_sevenDistinct_reindex

