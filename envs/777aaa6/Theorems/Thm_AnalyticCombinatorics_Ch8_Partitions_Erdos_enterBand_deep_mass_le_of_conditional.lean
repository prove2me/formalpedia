-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_enterBand_deep_mass_le_of_conditional
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.enterBand_deep_mass_le_of_conditional
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:01:50.334499+00:00
-- url     : https://prove2.me/theorems/0e128d27-ceb4-48d1-a616-013832c6182f
-- title:
--   A conditional first-entrance overshoot bound
-- statement:
--   First-entrance overshoot estimate assumes a conditional hazard-ratio bound. A per-step tail bound alone is insufficient and not substituted.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma enterBand_deep_mass_le_of_conditional
--       {P : ℕ → ℕ → ℝ} {B : Finset ℕ} {deep : ℕ → Prop} [DecidablePred deep]
--       {M : ℝ} (hM0 : 0 ≤ M) (hPnn : ∀ n k, 0 ≤ P n k)
--       (hPsupp : ∀ m k, m ≤ k → P m k = 0)
--       (hcond : ∀ v, v ∉ B →
--           ∑ k ∈ B.filter (fun k => deep k), P v k ≤ M * ∑ k ∈ B, P v k)
--       {n : ℕ} (hn : n ∉ B) :
--       ∑ z ∈ B.filter (fun z => deep z), enterBandKer P B n z
--         ≤ M * ∑ z ∈ B, enterBandKer P B n z
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/EnterBandEscape.lean#L49. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RankBandEntrance
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# TASK T2-value, brick 2.1: the variable-band escape lemma (abstract conditional core)

The variable rank-band engine consumes an **escape** bound: for the first-entrance kernel into the
ceiling down-set `ceilBand R (A R)`, the mass landing strictly below rank `R` (the "overshoot") is
`≤ e R`, with `e R → 0`.

**Mathematical correction to the R6 design.**  The naive bound "overshoot `≤` the per-step rank-drop
tail `M`" is FALSE.  The overshoot is a *first-entrance* probability; a chain with high holding (small
per-step crossing probability `c(v)`) can overshoot with probability `→ 1` even when each individual
step's deep-crossing mass `a(v)` is tiny (concrete witness: `c(v)=a(v)=ε`, `s(v)=1−ε` gives
`esc = ε + (1−ε)esc = 1`).  The correct, provable, and engine-sufficient statement is **conditional**:
if at every off-band vertex the deep-crossing mass is `≤ M ·` (total crossing mass), then the
first-entrance overshoot is `≤ M`.  This `enterBand_deep_mass_le_of_conditional` closes by the clean
super-solution invariant `esc(v) ≤ M · tot(v)` with `tot ≡ 1` the certain-entrance total.

The remaining analytic input — turning the banked rank-drop tail majorant
(`Pker_rankDrop_tail_majorant`) into the *conditional* deep-crossing bound `a(v) ≤ M · c(v)` — is the
ratio `P(drop > A R | drop ≥ 1)`, which needs the embedded rank-change exit chain (brick 2.2) and the
per-drop minorization `rankDropKer v 1, v 2 ≥ η` (banked `Pker_rankDrop_minorization`) to lower-bound
`c(v) ≥ 2η`.

NEW file; imports the banked engine bricks and the banked tail majorant, does not modify them.
Opus-authored.
-/

open Filter Topology BigOperators

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.enterBand_deep_mass_le_of_conditional
    {P : ℕ → ℕ → ℝ} {B : Finset ℕ} {deep : ℕ → Prop} [DecidablePred deep]
    {M : ℝ} (hM0 : 0 ≤ M) (hPnn : ∀ n k, 0 ≤ P n k)
    (hPsupp : ∀ m k, m ≤ k → P m k = 0)
    (hcond : ∀ v, v ∉ B →
        ∑ k ∈ B.filter (fun k => deep k), P v k ≤ M * ∑ k ∈ B, P v k)
    {n : ℕ} (hn : n ∉ B) :
    ∑ z ∈ B.filter (fun z => deep z), enterBandKer P B n z
      ≤ M * ∑ z ∈ B, enterBandKer P B n z := by sorry
