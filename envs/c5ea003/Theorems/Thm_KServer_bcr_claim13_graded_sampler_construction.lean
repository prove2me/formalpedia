-- Prove2me | Theorems.Thm_KServer_bcr_claim13_graded_sampler_construction
-- name    : KServer.bcr_claim13_graded_sampler_construction
-- status  : Open
-- author  : @kwal0203
-- created : 2026-10-30T17:47:18.730904+00:00
-- url     : https://prove2.me/theorems/3143ecc2-3316-4739-9910-81bffd1cb8e5
-- title:
--   BCR product race from a graded adaptive sampling program
-- statement:
--   Fix $0<\alpha\le1$, an integer $\beta\ge2$, and $w$ satisfying
--
--   $$a=\alpha\beta\le10^{-6},\qquad \alpha(w+1)^2>1.$$
--
--   Assume the mission's tight level-$w$ chunk invariant. There is a nonnegative-weight chunk certificate on the next-level space with the existing request, filtration, offline-cost, and online-escape axioms, constant initial chunk information, nonempty chunks, and nonnegative ceiling $c$, escape price $p_{\rm esc}$, and Doob-jump bound $j$ satisfying
--
--   $$p_{\rm esc}\le\beta3^w,\qquad c+j\le\frac{11}{8}3^w.$$
--
--   Its outcome space is identified by a bijection $e$ with a finite Boolean cube. Coordinate biases $\theta_i\in[0,1]$ give its product weights. There are $N$ race steps, preceded by $K$ seed reads, and an adaptive coordinate-selection program. Each seed coordinate has a level. For every possible transcript and every program time $t<K+N$, the program selects a coordinate at level $t$.
--
--   Let $T_x^t$ denote its transcript after $t$ reads from seed vector $x$. At race step $r<N$, two outcomes have the same race information label precisely when
--
--   $$T_{e\omega}^{K+r}=T_{e\omega'}^{K+r}.$$
--
--   The selected race coordinate is
--
--   $$I_r(\omega)=\operatorname{choose}(K+r,T_{e\omega}^{K+r}).$$
--
--   The race starts at state zero. Its state $S_r$ and nonnegative step sizes $L_r,R_r$ are constant on information atoms, with $L_r+R_r>0$. The selected coordinate has bias and branch value
--
--   $$\theta_{I_r(\omega)}=\frac{R_r(\omega)}{L_r(\omega)+R_r(\omega)},\qquad B_r(\omega)=(e\omega)_{I_r(\omega)}.$$
--
--   The state advances by $L_r$ on the true branch and by $-R_r$ on the false branch. Put $s=\sqrt a\,w$, and let $A$ be the actual expected total chunk size. The local moment budgets and stage accounting remain
--
--   $$\frac{s^2}{4}\le\sum_{r<N}\mathbb E[L_rR_r],$$
--
--   $$\sum_{r<N}\mathbb E\left[L_rR_r\left(6S_r^2+4S_r(L_r-R_r)+L_r^2-L_rR_r+R_r^2\right)\right]\le4s^4,$$
--
--   $$A\ge\left(3aw^2+\frac12\mathbb E|S_N|\right)3^w.$$
--
--   This is an open sufficient construction interface expressed by an explicit causal sampling program. The prelude permits earlier random sampling before the race begins. The selected-coordinate measurability and seed freshness required by the existing product-race frontier follow from the independent transcript-causality theorem.
--
--   **Formalization Note** Race labels are separate from the chunk filtration. The Doob-jump bound is required on positive-weight outcomes. The requests and every numerical bound remain construction obligations. This is a proposed sampling implementation for the platform's tight-price adaptation, not a claim that BCR's unmodified stopping rule satisfies these constants or that an arbitrary existing certificate already has this program realization.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1, stage 2a and stopping rule (1), and Section 4.2, equations (3)–(4), printed pp. 16–19. Proposed graded-transcript realization of platform frontier KServer.bcr_claim13_product_race_construction (790d28b5-38ea-435c-a70d-efe2302a8153). The tight numerical and geometric obligations remain explicit and open.

import Definitions.Def_KServer_binary_read_trace
import Definitions.Def_KServer_bcr_induction_tight
import Definitions.Def_KServer_nonneg_chunk_system
open KServer

theorem KServer.bcr_claim13_graded_sampler_construction (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β) (hsmall : α * (β : ℝ) ≤ 1 / 10 ^ 6)
    (w : ℕ) (hw : 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2)
    (hC : BCRInductiveChunksTight α β hβ w) :
    ∃ cB jb pe : ℝ, 0 ≤ cB ∧ 0 ≤ jb ∧ 0 ≤ pe ∧
      ∃ C : @NonnegChunkSystemB (bcrLevel2 β hβ (w + 1)).carrier
          (bcrLevel2 β hβ (w + 1)).metric
          (bcrLevel2 β hβ (w + 1)).s (bcrLevel2 β hβ (w + 1)).t
          0 cB 0 pe 0,
        ∃ (N : ℕ) (S L R : ℕ → C.Ω → ℝ) (H : ℕ → C.Ω → ℕ) (B : ℕ → C.Ω → Bool)
          (d : ℕ) (p : Fin d → ℝ) (e : C.Ω ≃ (Fin d → Bool)) (I : ℕ → C.Ω → Fin d)
          (K : ℕ) (grade : Fin d → ℕ) (choose : ℕ → (ℕ → Bool) → Fin d),
          (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧
          (∀ ω, C.P ω = ∏ i, if (e ω) i then p i else 1 - p i) ∧
          (∀ ω, S 0 ω = 0) ∧
          (∀ j < N, ∀ ω, 0 ≤ L j ω ∧ 0 ≤ R j ω ∧ 0 < L j ω + R j ω) ∧
          (∀ j < N, ∀ ω ω', H j ω = H j ω' →
            S j ω = S j ω' ∧ L j ω = L j ω' ∧ R j ω = R j ω') ∧
          (∀ j < N, ∀ ω, S (j + 1) ω =
            if B j ω then S j ω + L j ω else S j ω - R j ω) ∧
          (∀ n < K + N, ∀ history : ℕ → Bool, grade (choose n history) = n) ∧
          (∀ j < N, ∀ ω ω', H j ω = H j ω' ↔
            binaryReadTrace choose (e ω) (K + j) = binaryReadTrace choose (e ω') (K + j)) ∧
          (∀ j < N, ∀ ω, I j ω =
            choose (K + j) (binaryReadTrace choose (e ω) (K + j))) ∧
          (∀ j < N, ∀ ω, p (I j ω) = R j ω / (L j ω + R j ω)) ∧
          (∀ j < N, ∀ ω, B j ω = (e ω) (I j ω)) ∧
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
