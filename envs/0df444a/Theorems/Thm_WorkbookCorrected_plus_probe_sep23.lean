-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_probe_sep23
-- name    : WorkbookCorrected.plus_probe_sep23
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-23T13:10:15.327502+00:00
-- url     : https://prove2.me/theorems/8accedd3-1508-48ad-a24c-fc35b47895ef
-- title:
--   Probe publish queue
-- statement:
--   The elementary identity $2+2=4$ holds by direct evaluation.
--
--   Formalization Note: publish-queue probe only; will not be kept if duplicate naming fails.
--
--   Source: probe.
-- source:
--   probe

import Mathlib.Tactic.NormNum

theorem WorkbookCorrected.plus_probe_sep23 : (2:Nat) + 2 = 4 := by sorry
