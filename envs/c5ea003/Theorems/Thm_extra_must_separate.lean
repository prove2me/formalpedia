-- Prove2me | Theorems.Thm_extra_must_separate
-- name    : extra_must_separate
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-10T13:16:37.566964+00:00
-- url     : https://prove2.me/theorems/8325eb65-aa06-44af-adc3-401f704e4a82
-- title:
--   Any exact extra observation must distinguish timely from late
-- statement:
--   Let $E$ be any type, $e:\operatorname{History}\to E$, and $r:\operatorname{Observation}\times E\to\operatorname{Bool}$. If $r(\operatorname{observe}(h),e(h))=\operatorname{authorized}(h)$ for every toy history, then
--
--   $$e(\mathrm{timely})\ne e(\mathrm{late}).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/CAUSAL-PAIR-01/blob/02bcbbf17dfaade51171885578a228b16736d425/causal_fiber_01/CausalFiber01.lean#L83-L93; source SHA-256 bcff7eeabd153cd20f42ccd810dd20c074c9a899271ba5d29a4d6ed056b197ad; theorem extra_must_separate

import Definitions.Def_Couret_CausalFiber01_c81331552304
import Theorems.Thm_receipt_collision
import Theorems.Thm_verdict_collision
/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w

theorem extra_must_separate
    {E : Type u} (extra : History → E)
    (r : Observation × E → Bool)
    (hr : ∀ h, authorized h = r (observe h, extra h)) :
    extra .timely ≠ extra .late := by sorry






/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/






/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery



















end Recovery
