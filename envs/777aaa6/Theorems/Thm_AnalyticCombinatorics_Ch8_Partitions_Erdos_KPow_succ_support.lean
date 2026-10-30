-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_KPow_succ_support
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.KPow_succ_support
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T13:57:25.967272+00:00
-- url     : https://prove2.me/theorems/edca88ee-4143-468b-b6e2-0ad8cb1ac3a2
-- title:
--   Support of successor predecessor-kernel powers
-- statement:
--   Let $P:\mathbb{N}\times\mathbb{N}\to\mathbb{R}$ be arbitrary. Define the predecessor-truncated powers by
--
--   $$
--   K_0(n,k)=\delta_{nk},\qquad
--   K_{m+1}(n,k)=\sum_{j=0}^{n-1}P(n,j)K_m(j,k).
--   $$
--
--   Every sum is finite, with the empty sum interpreted as zero. For all $L,n,k\in\mathbb{N}$ with $n\le k$,
--
--   $$
--   K_{L+1}(n,k)=0.
--   $$
--
--   Thus every positive power is strictly lower triangular. No sign or stochasticity assumption on $P$ is required.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/KernelPow.lean#L53. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelPow
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin (File B): kernel composition and powers

Composition `KComp P Q n k = ∑_{j<n} P n j · Q j k` and the `L`-fold power `KPow L P` of a predecessor
kernel.  Proves nonnegativity and (strict) predecessor-support preservation by induction on `L` — the
algebraic foundation for the finite-time Doeblin overlap and the `P^L`-harmonic identity for `hitVal`.
The identity kernel `KPow 0 = δ(k=n)` forces the *strict* support `n < k → · = 0`.  Opus-authored.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.KPow_succ_support {P : ℕ → ℕ → ℝ} (L : ℕ) {n k : ℕ} (hnk : n ≤ k) :
    KPow (L + 1) P n k = 0 := by sorry
