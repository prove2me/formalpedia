-- Prove2me | solution 1 for Couret.DecisionInterface.factorization_on_image_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T17:02:31.761003+00:00
-- url     : https://prove2.me/submissions/71d2e51e-e8af-43c5-9d64-fd318ea629ab

import Definitions.Def_Couret_DecisionInterface_d4e860afd684
import Init

/- Source-only draft: NOT compiled in this package. No `sorry` placeholders.
   This module states the logical interface, not the cost/parity theorem.
   No connection to the Python implementation is formally proved here. -/
set_option autoImplicit false

universe u v w t
namespace Couret.DecisionInterface
variable {X : Type u} {Y : Type v} {A : Type w} {B : Type t}

























theorem inducedDecision_correct (O : X → Y) (D : X → A)
    (h : FibreConstant O D) (x : X) :
    inducedDecision O D ⟨O x, ⟨x, rfl⟩⟩ = D x := by
  unfold inducedDecision
  exact h _ _ (Classical.choose_spec (show ∃ z : X, O z = O x from ⟨x, rfl⟩))

theorem p2m_local_factorization_on_image_iff (O : X → Y) (D : X → A) :
    (∃ f : ObservedImage O → A,
      ∀ x : X, f ⟨O x, ⟨x, rfl⟩⟩ = D x) ↔ FibreConstant O D := by
  constructor
  · intro hf x y hxy
    obtain ⟨f, hf⟩ := hf
    have hi : (⟨O x, ⟨x, rfl⟩⟩ : ObservedImage O) = ⟨O y, ⟨y, rfl⟩⟩ :=
      Subtype.ext hxy
    exact (hf x).symm.trans ((congrArg f hi).trans (hf y))
  · intro h
    exact ⟨inducedDecision O D, inducedDecision_correct O D h⟩



end Couret.DecisionInterface

universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {X : Type p2m_u_0} {Y : Type p2m_u_1} {A : Type p2m_u_2} (O : X → Y) (D : X → A),
  Iff
    (@Exists.{max (p2m_u_1 + 1) (p2m_u_2 + 1)} (@Couret.DecisionInterface.ObservedImage.{p2m_u_0, p2m_u_1} X Y O → A)
      fun f =>
      ∀ (x : X),
        @Eq.{p2m_u_2 + 1} A
          (f
            (@Subtype.mk.{p2m_u_1 + 1} Y (fun y => @Exists.{p2m_u_0 + 1} X fun x => @Eq.{p2m_u_1 + 1} Y (O x) y) (O x)
              (@Exists.intro.{p2m_u_0 + 1} X (fun x_1 => @Eq.{p2m_u_1 + 1} Y (O x_1) (O x)) x
                (@rfl.{p2m_u_1 + 1} Y (O x)))))
          (D x))
    (@Couret.DecisionInterface.FibreConstant.{p2m_u_0, p2m_u_1, p2m_u_2} X Y A O D) := @_root_.Couret.DecisionInterface.p2m_local_factorization_on_image_iff

