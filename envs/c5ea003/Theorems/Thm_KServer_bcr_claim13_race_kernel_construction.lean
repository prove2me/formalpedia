-- Prove2me | Theorems.Thm_KServer_bcr_claim13_race_kernel_construction
-- name    : KServer.bcr_claim13_race_kernel_construction
-- status  : Open
-- author  : @kwal0203
-- created : 2026-10-30T16:53:36.180901+00:00
-- url     : https://prove2.me/theorems/00ff9ed0-68d4-410d-8b05-ee06ce049c88
-- title:
--   BCR race construction with transition and local moment budgets
-- statement:
--   Fix $0<\alpha\le1$, an integer $\beta\ge2$, and $w$ with
--
--   $$a=\alpha\beta\le10^{-6},\qquad \alpha(w+1)^2>1.$$
--
--   Assume the mission's tight level-$w$ chunk invariant. On the next-level space there is a chunk system $C$ satisfying the existing request-feasibility, offline-cost, filtration, and online-escape axioms, with nonnegative ceiling $c$, escape price $p$, and Doob-jump bound $j$, constant initial information, and nonempty chunks. Its budgets are
--
--   $$p\le\beta3^w,\qquad c+j\le\frac{11}{8}3^w.$$
--
--   There are a finite number $N$ of race steps and real arrays $S_t,L_t,R_t$ on the same outcome space, with $S_0=0$, nonnegative step sizes, and $L_t+R_t>0$. For each $t<N$ and every real test function $f$, they satisfy the averaged transition law
--
--   $$\mathbb E[f(S_{t+1})]=\mathbb E\left[\frac{R_t}{L_t+R_t}f(S_t+L_t)+\frac{L_t}{L_t+R_t}f(S_t-R_t)\right].$$
--
--   Put $s=\sqrt a\,w$ and let $A$ be the actual expected total chunk size. The local budgets and stage accounting are
--
--   $$\frac{s^2}{4}\le\sum_{t<N}\mathbb E[L_tR_t],$$
--
--   $$\sum_{t<N}\mathbb E\left[L_tR_t\left(6S_t^2+4S_t(L_t-R_t)+L_t^2-L_tR_t+R_t^2\right)\right]\le4s^4,$$
--
--   $$A\ge\left(3aw^2+\frac12\mathbb E|S_N|\right)3^w.$$
--
--   This is an open construction certificate for the existing frontier. It replaces terminal second- and fourth-moment requirements with an explicit transition law and local accumulated budgets. The random requests, these budgets, and the tight information and escape-price bounds still have to be constructed.
--
--   **Formalization Note** This is a sufficient interface for the platform's tight-price adaptation, not a verbatim theorem proved in BCR's paper. Neither the accumulated budgets nor the Doob-jump bound is inferred from a size window. No claim is made that BCR's unmodified stopping rule satisfies these constants. A stopped path can be kept fixed by setting $L_t=0,R_t=1$ afterwards.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1, stage 2a (transition probabilities), and Section 4.2, equations (3) and (4), printed pp. 16–19. Proposed local-transition certificate for platform frontier KServer.bcr_claim13_race_moment_construction (54c6314c-9b95-40cf-81f5-75d7d5be43bf). The tight price/jump and numerical moment budgets remain explicit open construction obligations.

import Definitions.Def_KServer_bcr_induction_tight
import Definitions.Def_KServer_chunk_cond
open KServer

theorem KServer.bcr_claim13_race_kernel_construction (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β) (hsmall : α * (β : ℝ) ≤ 1 / 10 ^ 6)
    (w : ℕ) (hw : 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2)
    (hC : BCRInductiveChunksTight α β hβ w) :
    ∃ cB jb pe : ℝ, 0 ≤ cB ∧ 0 ≤ jb ∧ 0 ≤ pe ∧
      ∃ C : @ChunkSystemB (bcrLevel2 β hβ (w + 1)).carrier
          (bcrLevel2 β hβ (w + 1)).metric
          (bcrLevel2 β hβ (w + 1)).s (bcrLevel2 β hβ (w + 1)).t
          0 cB 0 pe 0,
        ∃ (N : ℕ) (S L R : ℕ → C.Ω → ℝ),
          (∀ ω, S 0 ω = 0) ∧
          (∀ j < N, ∀ ω, 0 ≤ L j ω ∧ 0 ≤ R j ω ∧ 0 < L j ω + R j ω) ∧
          (∀ j < N, ∀ f : ℝ → ℝ,
            (∑ ω, C.P ω * f (S (j + 1) ω)) =
              ∑ ω, C.P ω * (R j ω / (L j ω + R j ω) * f (S j ω + L j ω) +
                L j ω / (L j ω + R j ω) * f (S j ω - R j ω))) ∧
          (Real.sqrt (α * β) * (w : ℝ)) ^ 2 / 4 ≤
            (∑ j ∈ Finset.range N, ∑ ω, C.P ω * (L j ω * R j ω)) ∧
          (∑ j ∈ Finset.range N, ∑ ω, C.P ω *
            (L j ω * R j ω * (6 * S j ω ^ 2 + 4 * S j ω * (L j ω - R j ω) +
              L j ω ^ 2 - L j ω * R j ω + R j ω ^ 2))) ≤
            4 * (Real.sqrt (α * β) * (w : ℝ)) ^ 4 ∧
          (3 * (α * β) * (w : ℝ) ^ 2 + (∑ ω, C.P ω * |S N ω|) / 2) * 3 ^ w
            ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) ∧
          pe ≤ (β : ℝ) * 3 ^ w ∧
          cB + jb ≤ 11 / 8 * (3 : ℝ) ^ w ∧
          (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) ∧
          (∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) ∧
          C.DoobJumpBound jb := by sorry
