-- Prove2me | solution 1 for collision_no_factor
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-10T13:16:42.255228+00:00
-- url     : https://prove2.me/submissions/fa2e3679-10a0-4f70-80a0-fd30c52e6fb2

import Definitions.Def_Couret_CausalFiber01_c81331552304
import Theorems.Thm_factor_implies_fiber_constant
/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w





theorem p2m_local_collision_no_factor
    {H : Type u} {O : Type v} {V : Type w}
    (p : H → O) (v : H → V)
    (a b : H) (same : p a = p b) (different : v a ≠ v b) :
    ¬ ∃ r : O → V, ∀ h, v h = r (p h) := by
  rintro ⟨r, hr⟩
  exact different (factor_implies_fiber_constant p v r hr a b same)






























/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/






/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery



















end Recovery

universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {H : Type p2m_u_0} {O : Type p2m_u_1} {V : Type p2m_u_2} (p : H → O) (v : H → V) (a b : H),
  @Eq.{p2m_u_1 + 1} O (p a) (p b) →
    @Ne.{p2m_u_2 + 1} V (v a) (v b) →
      Not (@Exists.{max (p2m_u_1 + 1) (p2m_u_2 + 1)} (O → V) fun r => ∀ (h : H), @Eq.{p2m_u_2 + 1} V (v h) (r (p h))) := @_root_.p2m_local_collision_no_factor

