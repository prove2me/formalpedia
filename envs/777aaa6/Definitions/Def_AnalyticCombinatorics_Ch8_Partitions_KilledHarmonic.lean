-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KilledHarmonic
-- name    : AnalyticCombinatorics_Ch8_Partitions_KilledHarmonic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:52:19.765643+00:00
-- url     : https://prove2.me/theorems/c6f397c0-9ec9-4f05-a002-c461b6a7b86b
-- title:
--   Killed Harmonic mathematical objects
-- statement:
--   The stopped kernel is the identity row below a rank cutoff and agrees with the original downward kernel above it.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/KilledHarmonic.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# R7 Fact B via Doeblin: the `P̃^L`-harmonic identity

A function `h` that is harmonic above a cutoff (`h n = ∑_{k<n} P n k · h k` for `rank n ≥ J`, and
`h n = φ n` below) is exactly harmonic for the *killed* kernel `P̃` summed over `range (n+1)`, and hence
for every power `KPowK L P̃`:  `h n = ∑_{k ∈ range (n+1)} (KPowK L P̃) n k · h k`.  Proof by induction on
`L` (one-step + `Finset.sum_comm` + support truncation).  This is the exact-harmonicity (η = 0) that
makes the Doeblin oscillation contraction error-free for `hitVal`.  Opus-authored.
-/

noncomputable section

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- Killed kernel: predecessor steps above the cutoff, identity-absorb on the boundary. -/
def killedKer (P : ℕ → ℕ → ℝ) (rank : ℕ → ℕ) (J : ℕ) : ℕ → ℕ → ℝ :=
  fun n k => if rank n < J then (if k = n then 1 else 0) else P n k

variable {P : ℕ → ℕ → ℝ} {rank : ℕ → ℕ} {J : ℕ} {h φ : ℕ → ℝ}

end AnalyticCombinatorics.Ch8.Partitions.Erdos


