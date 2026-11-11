-- Prove2me | solution 1 for sound_policy_iff_uniform
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-10T13:16:42.247863+00:00
-- url     : https://prove2.me/submissions/3b12de20-cd22-4595-a6b5-c1b3d49dfe23

import Definitions.Def_Couret_CausalFiber01_c81331552304
/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w




































/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/




theorem p2m_local_sound_policy_iff_uniform
    {H : Type u} {O : Type v} (p : H → O) (allowed : H → Prop)
    (permit : O → Prop) :
    (∀ h, permit (p h) → allowed h) ↔
      (∀ o, permit o → UniformlyAllowed p allowed o) := by
  constructor
  · intro sound o hp h he
    apply sound h
    rw [he]
    exact hp
  · intro uniform h hp
    exact uniform (p h) hp h rfl

/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery



















end Recovery

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {H : Type p2m_u_0} {O : Type p2m_u_1} (p : H → O) (allowed : H → Prop) (permit : O → Prop),
  Iff (∀ (h : H), permit (p h) → allowed h) (∀ (o : O), permit o → @UniformlyAllowed.{p2m_u_0, p2m_u_1} H O p allowed o) := @_root_.p2m_local_sound_policy_iff_uniform

