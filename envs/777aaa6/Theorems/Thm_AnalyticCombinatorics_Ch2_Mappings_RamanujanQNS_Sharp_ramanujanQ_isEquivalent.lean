-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch2_Mappings_RamanujanQNS_Sharp_ramanujanQ_isEquivalent
-- name    : AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.Sharp.ramanujanQ_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:49:35.710782+00:00
-- url     : https://prove2.me/theorems/cc9031c2-58cb-49f4-a4eb-ad20bfaf35a3
-- title:
--   Sharp square-root asymptotic of the finite Ramanujan Q-function
-- statement:
--   For a natural number $n$, define the real finite sum
--
--   $$Q(n)=\sum_{k=0}^{n-1}\prod_{j=1}^{k}\left(1-\frac{j}{n}\right),$$
--
--   with the empty product equal to one and $Q(0)=0$ by the empty sum. As $n$ tends to infinity through natural numbers,
--
--   $$Q(n)\sim\sqrt{\frac{\pi n}{2}}.$$
--
--   Equivalently, the ratio tends to one on the eventual positive-index domain. This is a statement about the displayed finite sum; no identification with a random-mapping expectation, stopping time or probability law is assumed.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/RamanujanQSharp.lean#L516. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_RamanujanQ
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Sharp lower asymptotic for Ramanujan's Q-function

This file proves the missing lower comparison for Ramanujan's finite
`Q`-function and upgrades the previously banked upper bound to the sharp
equivalence `Q(n) ~ sqrt (pi * n / 2)`.
-/

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.Mappings AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

theorem AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.Sharp.ramanujanQ_isEquivalent :
    (fun n : ℕ => ramanujanQ n) ~[atTop]
      (fun n : ℕ => Real.sqrt (Real.pi * (n : ℝ) / 2)) := by sorry
