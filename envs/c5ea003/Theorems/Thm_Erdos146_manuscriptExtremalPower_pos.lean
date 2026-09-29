-- Prove2me | Theorems.Thm_Erdos146_manuscriptExtremalPower_pos
-- name    : Erdos146.manuscriptExtremalPower_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:54:06.255267+00:00
-- url     : https://prove2.me/theorems/7609aa43-406f-4485-982c-d821aa212130
-- title:
--   The extremal power is positive
-- statement:
--   Verification that the parameters of Section 6 exist. The construction needs a Hamming radius $\tau \in (0, 1/2)$ and a sampling exponent $\beta$ with $A(\tau) < \beta < C(\tau)$, where $A(\tau) = \kappa + \tau\log_2 3$ and $C(\tau) = 2h(\tau) - 1$; the source verifies at the end of Section 6 that such parameters exist. The exponent $3/2 + \varepsilon$ of Theorem 1.2 is positive.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L18128-L18131

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.manuscriptExtremalPower_pos :
    0 < manuscriptExtremalPower := by sorry
