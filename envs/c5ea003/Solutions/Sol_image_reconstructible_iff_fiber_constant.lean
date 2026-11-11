-- Prove2me | solution 1 for image_reconstructible_iff_fiber_constant
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-10T13:16:42.069926+00:00
-- url     : https://prove2.me/submissions/29b38a35-10af-4336-a790-186cc36672b9

import Definitions.Def_Couret_CausalFiber01_c81331552304
/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w









theorem p2m_local_image_reconstructible_iff_fiber_constant
    {H : Type u} {O : Type v} {V : Type w}
    (p : H → O) (v : H → V) :
    ImageReconstructible p v ↔ FiberConstant p v := by
  constructor
  · rintro ⟨r, hr⟩ a b hab
    calc
      v a = r (p a) ⟨a, rfl⟩ := hr a
      _ = r (p b) ⟨b, rfl⟩ := by
        have hx : (⟨p a, ⟨a, rfl⟩⟩ : {o : O // ∃ h : H, p h = o}) =
            ⟨p b, ⟨b, rfl⟩⟩ := Subtype.ext hab
        exact congrArg
          (fun x : {o : O // ∃ h : H, p h = o} => r x.val x.property)
          hx
      _ = v b := (hr b).symm
  · intro hc
    classical
    refine ⟨(fun o ho => v (Classical.choose ho)), ?_⟩
    intro h
    let ho : ∃ h' : H, p h' = p h := ⟨h, rfl⟩
    exact hc h (Classical.choose ho) (Classical.choose_spec ho).symm


























/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/






/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery



















end Recovery

universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {H : Type p2m_u_0} {O : Type p2m_u_1} {V : Type p2m_u_2} (p : H → O) (v : H → V),
  Iff (@ImageReconstructible.{p2m_u_0, p2m_u_1, p2m_u_2} H O V p v)
    (@FiberConstant.{p2m_u_0, p2m_u_1, p2m_u_2} H O V p v) := @_root_.p2m_local_image_reconstructible_iff_fiber_constant

