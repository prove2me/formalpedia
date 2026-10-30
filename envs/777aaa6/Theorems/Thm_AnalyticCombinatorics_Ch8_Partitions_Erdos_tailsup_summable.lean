-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_tailsup_summable
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.tailsup_summable
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:48:33.593761+00:00
-- url     : https://prove2.me/theorems/4a9d728c-02ff-4084-8eb3-5b791461a66c
-- title:
--   Tail-sup summability in the globally forced zero regime
-- statement:
--   Let W:Nat→Real be nonnegative and globally bounded above, and let0<=q<1. Assume the displayed contraction for every natural R, with arbitrary B:Nat. These global hypotheses force W≡0, so every displayed tail supremum is0 and the resulting series is summable. This is the zero-sequence regime; it is not a summability producer for a nonzero oscillation sequence.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma tailsup_summable {W : ℕ → ℝ} {q M : ℝ} {B : ℕ}
--       (hWnn : ∀ R, 0 ≤ W R) (hWbd : ∀ R, W R ≤ M)
--       (hq0 : 0 ≤ q) (hq1 : q < 1)
--       (hcontract : ∀ R, W R ≤ q * sSup (W '' {s | R - B ≤ s})) :
--       Summable (fun R => sSup (W '' {s | R ≤ s}))
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/TailSup.lean#L17. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: the tail-sup of block oscillation is summable

The §9 connection's key device: if block oscillation `W ≥ 0` is bounded and satisfies the slab
contraction `W R ≤ q · sSup(W '' {s ≥ R−B})` (`0 ≤ q < 1`), then its tail-sup
`V R := sSup(W '' {s ≥ R})` is monotone-dominated, so `V R ≤ q · V(R−B)`, hence `Summable V`.  This
turns the local (comparable-rank) contraction into a global summable bound, resolving the far-pair
obstruction.  `csSup`-based.  Opus-authored.
-/

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.tailsup_summable {W : ℕ → ℝ} {q M : ℝ} {B : ℕ}
    (hWnn : ∀ R, 0 ≤ W R) (hWbd : ∀ R, W R ≤ M)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ R, W R ≤ q * sSup (W '' {s | R - B ≤ s})) :
    Summable (fun R => sSup (W '' {s | R ≤ s})) := by sorry
