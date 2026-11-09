-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.zip_mapped_eq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:01.342979+00:00
-- url     : https://prove2.me/submissions/2cbbd2bd-a36f-491f-8a2c-d257ce080eb5

import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity





theorem p2m_local_zip_mapped_eq {α β γ : Type*} (L : List α) (R : List β)
    (f : α → γ) (g : β → γ) (h : L.map f=R.map g) :
    ∀ a b, (a,b)∈L.zip R → f a=g b := by
  induction L generalizing R with
  | nil => simp
  | cons a as ih =>
    cases R with
    | nil => simp
    | cons b bs =>
      have hs : f a=g b ∧ as.map f=bs.map g := List.cons.inj h
      intro c d hm
      simp only [List.zip_cons_cons,List.mem_cons] at hm
      rcases hm with he|he
      · cases he
        exact hs.1
      · exact ih bs hs.2 c d he

end Couret.InterIA.SingletonNecessity

universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {α : Type p2m_u_0} {β : Type p2m_u_1} {γ : Type p2m_u_2} (L : List.{p2m_u_0} α) (R : List.{p2m_u_1} β) (f : α → γ)
  (g : β → γ),
  @Eq.{p2m_u_2 + 1} (List.{p2m_u_2} γ) (@List.map.{p2m_u_0, p2m_u_2} α γ f L) (@List.map.{p2m_u_1, p2m_u_2} β γ g R) →
    ∀ (a : α) (b : β),
      @Membership.mem.{max p2m_u_1 p2m_u_0, max p2m_u_0 p2m_u_1} (Prod.{p2m_u_0, p2m_u_1} α β)
          (List.{max p2m_u_1 p2m_u_0} (Prod.{p2m_u_0, p2m_u_1} α β))
          (@List.instMembership.{max p2m_u_0 p2m_u_1} (Prod.{p2m_u_0, p2m_u_1} α β))
          (@List.zip.{p2m_u_0, p2m_u_1} α β L R) (@Prod.mk.{p2m_u_0, p2m_u_1} α β a b) →
        @Eq.{p2m_u_2 + 1} γ (f a) (g b) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_zip_mapped_eq

