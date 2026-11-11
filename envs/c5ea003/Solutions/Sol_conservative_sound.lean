-- Prove2me | solution 1 for conservative_sound
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-10T13:16:13.495556+00:00
-- url     : https://prove2.me/submissions/17c14274-981e-4053-89e2-a48d20202047

import Definitions.Def_Couret_CausalFiber01_c81331552304
/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w




































/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/


theorem p2m_local_conservative_sound
    {H : Type u} {O : Type v} (p : H → O) (allowed : H → Prop)
    (h : H) (permit : UniformlyAllowed p allowed (p h)) : allowed h :=
  permit h rfl



/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery



















end Recovery

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {H : Type p2m_u_0} {O : Type p2m_u_1} (p : H → O) (allowed : H → Prop) (h : H),
  @UniformlyAllowed.{p2m_u_0, p2m_u_1} H O p allowed (p h) → allowed h := @_root_.p2m_local_conservative_sound

