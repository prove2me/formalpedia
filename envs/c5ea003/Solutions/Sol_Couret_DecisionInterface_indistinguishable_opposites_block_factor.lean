-- Prove2me | solution 1 for Couret.DecisionInterface.indistinguishable_opposites_block_factor
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T17:02:48.59198+00:00
-- url     : https://prove2.me/submissions/0efb6b0e-90b8-4e0c-9690-cb61375488a4

import Definitions.Def_Couret_DecisionInterface_d4e860afd684
import Init

/- Source-only draft: NOT compiled in this package. No `sorry` placeholders.
   This module states the logical interface, not the cost/parity theorem.
   No connection to the Python implementation is formally proved here. -/
set_option autoImplicit false

universe u v w t
namespace Couret.DecisionInterface
variable {X : Type u} {Y : Type v} {A : Type w} {B : Type t}





























theorem p2m_local_indistinguishable_opposites_block_factor (O : X → Y) (D : X → A)
    (x y : X) (hobs : O x = O y) (hne : D x ≠ D y) :
    ¬ ∃ f : Y → A, ∀ z : X, f (O z) = D z := by
  intro hf
  obtain ⟨f, hf⟩ := hf
  exact hne ((hf x).symm.trans ((congrArg f hobs).trans (hf y)))

end Couret.DecisionInterface

universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {X : Type p2m_u_0} {Y : Type p2m_u_1} {A : Type p2m_u_2} (O : X → Y) (D : X → A) (x y : X),
  @Eq.{p2m_u_1 + 1} Y (O x) (O y) →
    @Ne.{p2m_u_2 + 1} A (D x) (D y) →
      Not (@Exists.{max (p2m_u_1 + 1) (p2m_u_2 + 1)} (Y → A) fun f => ∀ (z : X), @Eq.{p2m_u_2 + 1} A (f (O z)) (D z)) := @_root_.Couret.DecisionInterface.p2m_local_indistinguishable_opposites_block_factor

