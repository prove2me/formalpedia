-- Prove2me | Theorems.Thm_missing_refused
-- name    : missing_refused
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-10T13:16:35.761675+00:00
-- url     : https://prove2.me/theorems/cce95175-8d51-4446-a5bd-f82dcf83d07e
-- title:
--   The missing toy history is refused
-- statement:
--   In the four-state toy model, $\operatorname{authorized}(\mathrm{missing})=\mathrm{false}$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/CAUSAL-PAIR-01/blob/02bcbbf17dfaade51171885578a228b16736d425/causal_fiber_01/CausalFiber01.lean#L95-L95; source SHA-256 bcff7eeabd153cd20f42ccd810dd20c074c9a899271ba5d29a4d6ed056b197ad; theorem missing_refused

import Definitions.Def_Couret_CausalFiber01_c81331552304
/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w

theorem missing_refused : authorized .missing = false := by sorry




/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/






/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery



















end Recovery
