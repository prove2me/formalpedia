-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_modelIntegral_ge
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.modelIntegral_ge
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:32:35.094095+00:00
-- url     : https://prove2.me/theorems/a6635e42-7190-4183-9696-d07f4ff44f98
-- title:
--   A positive lower bound for the rank-drop model integral
-- statement:
--   A positive model-integral lower bound; it is an ingredient of a geometric rate, not the full all-threshold partition tail minorant.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma modelIntegral_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
--       (b - a) * ((Real.pi ^ 2 / 6) * a * Real.exp (-(C / 2) * b)) ≤ Model.modelIntegral C a b
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/RankDropGeoMinor.lean#L39. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ModelAssembly
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# TASK T2-ceiling, L5-escape core: the per-drop GEOMETRIC minorant

The banked `Pker_rankDrop_minorization` only minorizes drops `1` and `2`
(`rankDropKer v 1, v 2 ≥ η`).  The escape super-solution (L5) needs a **geometric lower bound on the
rank-drop tail at every threshold** `g`:

  `∑_{d > g} rankDropKer v d ≥ c · e^{−γ' g}`  (eventually in `v`),

so that the conditional overshoot ratio `tail(g + A R)/tail(g)` is uniformly `≤ e R → 0`.  It suffices
to minorize each *single* drop `d` geometrically: `rankDropKer v d ≥ η_d` with `η_d ≳ d e^{−C d/3}`.

This file banks the reusable **integral lower bound**
`modelIntegral C a b ≥ (b − a) · (π²/6) · a · e^{−(C/2) b}` for `0 ≤ a < b` — the geometric-rate
ingredient (`e^{−(C/2) b}` with `b ≈ (2/3) d` ⟹ `e^{−C d/3}`) for the eventual per-drop minorant.

The full per-drop window minorant `rankDropKer v d ≥ η_d` (for each `d`, via a phase cover of `[0,1)`
by four windows whose `t`-bands scale with `d`, applied through `rankDropKer_ge_const_of_tband`) still
requires making that lemma's eventual-in-`v` threshold EXPLICIT in `(a,b,d)`, so that for a fixed
large `v` all drops `d ≲ √v` are simultaneously minorized (needed for the tail lower bound
`tail(g) ≥ c e^{−γ' g}` at a single `v`).

NEW file; imports the banked minorization/window bricks, does not modify them.  Opus-authored.
-/

open Filter Topology BigOperators

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

open AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.modelIntegral_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (b - a) * ((Real.pi ^ 2 / 6) * a * Real.exp (-(C / 2) * b)) ≤ Model.modelIntegral C a b := by sorry
