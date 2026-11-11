-- Prove2me | Theorems.Thm_conservative_sound
-- name    : conservative_sound
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-10T13:15:22.114197+00:00
-- url     : https://prove2.me/theorems/7beb46d6-358e-4f73-b9c4-7f731cb608aa
-- title:
--   Uniform permission on an observation fibre is sound for its actual history
-- statement:
--   Let $p:H\to O$ and $A:H\to\operatorname{Prop}$. If every history $h'$ with $p(h')=p(h)$ satisfies $A(h')$, then $A(h)$. Equivalently, $\operatorname{UniformlyAllowed}(p,A,p(h))$ implies $A(h)$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/CAUSAL-PAIR-01/blob/02bcbbf17dfaade51171885578a228b16736d425/causal_fiber_01/CausalFiber01.lean#L106-L109; source SHA-256 bcff7eeabd153cd20f42ccd810dd20c074c9a899271ba5d29a4d6ed056b197ad; theorem conservative_sound

import Definitions.Def_Couret_CausalFiber01_c81331552304
/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w




































/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/

theorem conservative_sound
    {H : Type u} {O : Type v} (p : H → O) (allowed : H → Prop)
    (h : H) (permit : UniformlyAllowed p allowed (p h)) : allowed h := by sorry




/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery



















end Recovery
