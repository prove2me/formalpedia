-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_umass_lt_of_occupation_unbounded
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_lt_of_occupation_unbounded
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:01:38.28614+00:00
-- url     : https://prove2.me/theorems/20aad161-29e0-4513-b75b-c7229cae2acc
-- title:
--   A coalescence comparison from unbounded occupation
-- statement:
--   Real-sequence implication from occupation being unbounded and a coalescence recursion; it supplies neither the concrete occupation bound nor a nonempty instance.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem umass_lt_of_occupation_unbounded (u g : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
--       (hu_nn : ∀ t, 0 ≤ u t) (hu0 : u 0 ≤ 1) (hg_nn : ∀ t, 0 ≤ g t)
--       (hrec : ∀ t, u (t + 1) ≤ u t - δ * (u t * g t))
--       (hgunb : ∀ K : ℝ, ∃ M, K ≤ ∑ t ∈ Finset.range M, g t)
--       (ε : ℝ) (hε : 0 < ε) :
--       ∃ M, u M ≤ ε
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/CoalesceBridge.lean#L22. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: the conditioned-walk coalescence bridge

Bridges the *stochastic* occupation lower bound (`occupation_unbounded_eta`, applied to the conditioned
walk `Ûmat = Umat/umass`) back to the *substochastic* coalescing mass `umass`.  The conditioned
coalescence recursion is `umass(t+1) ≤ umass(t) − δ·umass(t)·ĝ(t)` where `ĝ(t)` is the conditioned
window fraction; with the conditioned window occupation `∑ ĝ` unbounded, `umass → 0` (any threshold `ε`
is eventually beaten).  Pure real-sequence argument.  Opus-authored.
-/

open Finset

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_lt_of_occupation_unbounded (u g : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hu_nn : ∀ t, 0 ≤ u t) (hu0 : u 0 ≤ 1) (hg_nn : ∀ t, 0 ≤ g t)
    (hrec : ∀ t, u (t + 1) ≤ u t - δ * (u t * g t))
    (hgunb : ∀ K : ℝ, ∃ M, K ≤ ∑ t ∈ Finset.range M, g t)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M, u M ≤ ε := by sorry
