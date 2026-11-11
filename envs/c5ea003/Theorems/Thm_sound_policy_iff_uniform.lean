-- Prove2me | Theorems.Thm_sound_policy_iff_uniform
-- name    : sound_policy_iff_uniform
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-10T13:16:38.37134+00:00
-- url     : https://prove2.me/theorems/4f264f7e-102f-4426-a611-5c5cece4b6e4
-- title:
--   A sound observation policy permits only uniformly allowed fibres
-- statement:
--   Let $p:H\to O$, $A:H\to\operatorname{Prop}$ and $P:O\to\operatorname{Prop}$. Then
--
--   $$\bigl(\forall h,\;P(p(h))\Rightarrow A(h)\bigr)\iff\bigl(\forall o,\;P(o)\Rightarrow\forall h,\;p(h)=o\Rightarrow A(h)\bigr).$$
--
--   The right side is uniform permission over each permitted observation fibre, including vacuous fibres outside the image.
-- source:
--   Alexandre Couret, https://github.com/alexcour/CAUSAL-PAIR-01/blob/02bcbbf17dfaade51171885578a228b16736d425/causal_fiber_01/CausalFiber01.lean#L111-L122; source SHA-256 bcff7eeabd153cd20f42ccd810dd20c074c9a899271ba5d29a4d6ed056b197ad; theorem sound_policy_iff_uniform

import Definitions.Def_Couret_CausalFiber01_c81331552304
/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w




































/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/

theorem sound_policy_iff_uniform
    {H : Type u} {O : Type v} (p : H → O) (allowed : H → Prop)
    (permit : O → Prop) :
    (∀ h, permit (p h) → allowed h) ↔
      (∀ o, permit o → UniformlyAllowed p allowed o) := by sorry


/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery



















end Recovery
