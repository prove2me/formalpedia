-- Prove2me | Theorems.Thm_KServer_bcr_claim13_product_race_construction
-- name    : KServer.bcr_claim13_product_race_construction
-- status  : Open
-- author  : @kwal0203
-- created : 2026-10-30T17:33:38.823895+00:00
-- url     : https://prove2.me/theorems/790d28b5-38ea-435c-a70d-efe2302a8153
-- title:
--   BCR race construction from fresh independent Boolean seeds
-- statement:
--   Fix $0<\alpha\le1$, an integer $\beta\ge2$, and $w$ satisfying
--
--   $$a=\alpha\beta\le10^{-6},\qquad \alpha(w+1)^2>1.$$
--
--   Assume the mission's tight level-$w$ chunk invariant. There is a nonnegative-weight chunk certificate on the next-level space, retaining the existing request, filtration, offline-cost, and online-escape axioms, constant initial chunk information, nonempty chunks, nonnegative ceiling $c$, escape price $p_{\rm esc}$, and Doob-jump bound $j$. Its budgets are
--
--   $$p_{\rm esc}\le\beta3^w,\qquad c+j\le\frac{11}{8}3^w.$$
--
--   The finite outcome space is identified by a bijection $e$ with a Boolean cube of dimension $d$. It has fixed coordinate biases $\theta_i\in[0,1]$ and product weights
--
--   $$P(\omega)=\prod_i\begin{cases}\theta_i,&(e\omega)_i=1,\\1-\theta_i,&(e\omega)_i=0.\end{cases}$$
--
--   There are $N$ race steps with state $S_t$, nonnegative step sizes $L_t,R_t$ with positive sum, information labels $H_t$, branch choices $B_t$, and selected coordinate $I_t$. The state starts at zero. The state, step sizes, and selected coordinate are constant on every atom of $H_t$. The selected bit has bias and branch value
--
--   $$\theta_{I_t(\omega)}=\frac{R_t(\omega)}{L_t(\omega)+R_t(\omega)},\qquad B_t(\omega)=(e\omega)_{I_t(\omega)}.$$
--
--   The selected coordinate is fresh: changing only that seed bit leaves the current information label unchanged, for either replacement bit. The next state is the current state plus the left step on the true branch and the current state minus the right step otherwise.
--
--   Put $s=\sqrt a\,w$, and let $T$ be the actual expected total chunk size. The retained local moment budgets and stage accounting are
--
--   $$\frac{s^2}{4}\le\sum_{t<N}\mathbb E[L_tR_t],$$
--
--   $$\sum_{t<N}\mathbb E\left[L_tR_t\left(6S_t^2+4S_t(L_t-R_t)+L_t^2-L_tR_t+R_t^2\right)\right]\le4s^4,$$
--
--   $$T\ge\left(3aw^2+\frac12\mathbb E|S_N|\right)3^w.$$
--
--   This is an open sufficient construction interface using finitely many independent biased seeds and an explicit freshness condition. It supplies the probabilistic mechanism for the existing atomwise race frontier; the requests and all numerical budgets remain construction obligations.
--
--   **Formalization Note** Race information labels are separate from the chunk filtration. Biases at the endpoints are permitted because zero-weight outcomes are allowed. The Doob-jump bound is required on positive-weight outcomes. This is a proposed sufficient realization of the platform's tight-price adaptation, not a claim that BCR's unmodified stopping rule meets these numerical constants, or that every arbitrary race certificate already comes with this seed realization.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1, stage 2a (independent sampling and the left/right probabilities), and Section 4.2, equations (3)–(4), printed pp. 16–19. Proposed finite-seed construction interface for platform frontier KServer.bcr_claim13_nonneg_race_construction (31ba193d-1298-46ec-857e-4b87b48806c2). The numerical and tight price/jump budgets are retained as explicit open obligations.

import Definitions.Def_KServer_bcr_induction_tight
import Definitions.Def_KServer_nonneg_chunk_system
open KServer

theorem KServer.bcr_claim13_product_race_construction (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β) (hsmall : α * (β : ℝ) ≤ 1 / 10 ^ 6)
    (w : ℕ) (hw : 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2)
    (hC : BCRInductiveChunksTight α β hβ w) :
    ∃ cB jb pe : ℝ, 0 ≤ cB ∧ 0 ≤ jb ∧ 0 ≤ pe ∧
      ∃ C : @NonnegChunkSystemB (bcrLevel2 β hβ (w + 1)).carrier
          (bcrLevel2 β hβ (w + 1)).metric
          (bcrLevel2 β hβ (w + 1)).s (bcrLevel2 β hβ (w + 1)).t
          0 cB 0 pe 0,
        ∃ (N : ℕ) (S L R : ℕ → C.Ω → ℝ) (H : ℕ → C.Ω → ℕ) (B : ℕ → C.Ω → Bool)
          (d : ℕ) (p : Fin d → ℝ) (e : C.Ω ≃ (Fin d → Bool)) (I : ℕ → C.Ω → Fin d),
          (∀ i, 0 ≤ p i ∧ p i ≤ 1) ∧
          (∀ ω, C.P ω = ∏ i, if (e ω) i then p i else 1 - p i) ∧
          (∀ ω, S 0 ω = 0) ∧
          (∀ j < N, ∀ ω, 0 ≤ L j ω ∧ 0 ≤ R j ω ∧ 0 < L j ω + R j ω) ∧
          (∀ j < N, ∀ ω ω', H j ω = H j ω' →
            S j ω = S j ω' ∧ L j ω = L j ω' ∧ R j ω = R j ω') ∧
          (∀ j < N, ∀ ω, S (j + 1) ω =
            if B j ω then S j ω + L j ω else S j ω - R j ω) ∧
          (∀ j < N, ∀ ω ω', H j ω = H j ω' → I j ω = I j ω') ∧
          (∀ j < N, ∀ ω, p (I j ω) = R j ω / (L j ω + R j ω)) ∧
          (∀ j < N, ∀ ω, B j ω = (e ω) (I j ω)) ∧
          (∀ j < N, ∀ ω (b : Bool),
            H j (e.symm (Function.update (e ω) (I j ω) b)) = H j ω) ∧
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
