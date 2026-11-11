-- Prove2me | solution 1 for extra_must_separate
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-10T13:16:42.250178+00:00
-- url     : https://prove2.me/submissions/4965ea1f-928c-4c8e-ad95-4355c11039a9

import Definitions.Def_Couret_CausalFiber01_c81331552304
import Theorems.Thm_receipt_collision
import Theorems.Thm_verdict_collision
/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w






























theorem p2m_local_extra_must_separate
    {E : Type u} (extra : History → E)
    (r : Observation × E → Bool)
    (hr : ∀ h, authorized h = r (observe h, extra h)) :
    extra .timely ≠ extra .late := by
  intro he
  apply verdict_collision
  calc
    authorized .timely = r (observe .timely, extra .timely) := hr .timely
    _ = r (observe .late, extra .late) := by rw [receipt_collision, he]
    _ = authorized .late := (hr .late).symm





/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/






/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery



















end Recovery

universe p2m_u_0
theorem solution : ∀ {E : Type p2m_u_0} (extra : History → E) (r : Prod.{0, p2m_u_0} Observation E → Bool),
  (∀ (h : History), @Eq.{1} Bool (authorized h) (r (@Prod.mk.{0, p2m_u_0} Observation E (observe h) (extra h)))) →
    @Ne.{p2m_u_0 + 1} E (extra History.timely) (extra History.late) := @_root_.p2m_local_extra_must_separate

