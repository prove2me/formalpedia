-- Prove2me | Theorems.Thm_stale_refused
-- name    : stale_refused
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-10T13:16:40.638201+00:00
-- url     : https://prove2.me/theorems/405ad97f-ac17-4503-abed-7f8bd649be44
-- title:
--   The stale toy history is refused
-- statement:
--   In the four-state toy model, $\operatorname{authorized}(\mathrm{stale})=\mathrm{false}$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/CAUSAL-PAIR-01/blob/02bcbbf17dfaade51171885578a228b16736d425/causal_fiber_01/CausalFiber01.lean#L96-L96; source SHA-256 bcff7eeabd153cd20f42ccd810dd20c074c9a899271ba5d29a4d6ed056b197ad; theorem stale_refused

import Definitions.Def_Couret_CausalFiber01_c81331552304
/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w

theorem stale_refused : authorized .stale = false := by sorry



/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/






/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery



















end Recovery
