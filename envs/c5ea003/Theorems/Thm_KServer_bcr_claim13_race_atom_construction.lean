-- Prove2me | Theorems.Thm_KServer_bcr_claim13_race_atom_construction
-- name    : KServer.bcr_claim13_race_atom_construction
-- status  : Open
-- author  : @kwal0203
-- created : 2026-10-30T17:04:59.981085+00:00
-- url     : https://prove2.me/theorems/8d79a745-d157-47f2-a6ac-73f0af71834e
-- title:
--   BCR race construction with explicit atomwise branch probabilities
-- statement:
--   Fix $0<\alpha\le1$, an integer $\beta\ge2$, and $w$ with
--
--   $$a=\alpha\beta\le10^{-6},\qquad \alpha(w+1)^2>1.$$
--
--   Assume the mission's tight level-$w$ chunk invariant. On the next-level space there is a chunk system $C$ satisfying the existing request, filtration, offline-cost, and online-escape axioms, with nonnegative ceiling $c$, escape price $p$, and Doob-jump bound $j$, constant initial information, and nonempty chunks. Its tight budgets are
--
--   $$p\le\beta3^w,\qquad c+j\le\frac{11}{8}3^w.$$
--
--   On the same finite outcome space there are $N$ race steps, arrays $S_t,L_t,R_t$, information labels $H_t$, and Boolean branch choices $B_t$. The state starts at zero. Step sizes are nonnegative with $L_t+R_t>0$. The state and both step sizes are constant on each atom of $H_t$. The next state is
--
--   $$S_{t+1}=\begin{cases}S_t+L_t,&B_t=\mathrm{true},\\S_t-R_t,&B_t=\mathrm{false}.\end{cases}$$
--
--   For every $t<N$ and every atom $A$ of the race information partition, its true-branch mass is
--
--   $$P\bigl(A\cap\{B_t=\mathrm{true}\}\bigr)=\frac{R_t}{L_t+R_t}P(A),$$
--
--   where the ratio on the right is constant on that atom. Put $s=\sqrt a\,w$, and let $T_C$ be the actual expected total chunk size. The quantitative requirements are
--
--   $$\frac{s^2}{4}\le\sum_{t<N}\mathbb E[L_tR_t],$$
--
--   $$\sum_{t<N}\mathbb E\left[L_tR_t\left(6S_t^2+4S_t(L_t-R_t)+L_t^2-L_tR_t+R_t^2\right)\right]\le4s^4,$$
--
--   $$T_C\ge\left(3aw^2+\frac12\mathbb E|S_N|\right)3^w.$$
--
--   This open construction certificate specifies the source's conditional left/right selection rule directly. The averaged transition law for all test functions follows from the independently proved finite mixture lemma, rather than being a separate construction obligation.
--
--   **Formalization Note** The labels $H_t$ describe the race partitions; they are separate from the chunk-system filtration. This is a sufficient interface for the platform's tight-price adaptation, not a verbatim assertion proved in the paper. The numerical moment budgets, the actual requests, and the tight price and jump bounds remain open construction obligations. No claim is made that the paper's unmodified stopping rule satisfies these numerical budgets.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1, stage 2a (the probabilities p_L and p_R), and Section 4.2, equations (3)–(4), printed pp. 16–19. Proposed atomwise construction certificate for platform frontier KServer.bcr_claim13_race_kernel_construction (00ff9ed0-68d4-410d-8b05-ee06ce049c88). The pre-existing numerical and tight price/jump budgets remain open hypotheses of the construction.

import Definitions.Def_KServer_bcr_induction_tight
import Definitions.Def_KServer_chunk_cond
open KServer

theorem KServer.bcr_claim13_race_atom_construction (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β) (hsmall : α * (β : ℝ) ≤ 1 / 10 ^ 6)
    (w : ℕ) (hw : 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2)
    (hC : BCRInductiveChunksTight α β hβ w) :
    ∃ cB jb pe : ℝ, 0 ≤ cB ∧ 0 ≤ jb ∧ 0 ≤ pe ∧
      ∃ C : @ChunkSystemB (bcrLevel2 β hβ (w + 1)).carrier
          (bcrLevel2 β hβ (w + 1)).metric
          (bcrLevel2 β hβ (w + 1)).s (bcrLevel2 β hβ (w + 1)).t
          0 cB 0 pe 0,
        ∃ (N : ℕ) (S L R : ℕ → C.Ω → ℝ) (H : ℕ → C.Ω → ℕ) (B : ℕ → C.Ω → Bool),
          (∀ ω, S 0 ω = 0) ∧
          (∀ j < N, ∀ ω, 0 ≤ L j ω ∧ 0 ≤ R j ω ∧ 0 < L j ω + R j ω) ∧
          (∀ j < N, ∀ ω ω', H j ω = H j ω' →
            S j ω = S j ω' ∧ L j ω = L j ω' ∧ R j ω = R j ω') ∧
          (∀ j < N, ∀ ω, S (j + 1) ω =
            if B j ω then S j ω + L j ω else S j ω - R j ω) ∧
          (∀ j < N, ∀ ω₀,
            (∑ ω ∈ Finset.univ.filter (fun ω => H j ω = H j ω₀ ∧ B j ω = true), C.P ω) =
              (R j ω₀ / (L j ω₀ + R j ω₀)) *
                (∑ ω ∈ Finset.univ.filter (fun ω => H j ω = H j ω₀), C.P ω)) ∧
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
