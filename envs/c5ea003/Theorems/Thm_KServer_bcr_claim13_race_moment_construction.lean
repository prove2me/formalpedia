-- Prove2me | Theorems.Thm_KServer_bcr_claim13_race_moment_construction
-- name    : KServer.bcr_claim13_race_moment_construction
-- status  : Open
-- author  : @kwal0203
-- created : 2026-10-30T16:41:28.06266+00:00
-- url     : https://prove2.me/theorems/54c6314c-9b95-40cf-81f5-75d7d5be43bf
-- title:
--   BCR race construction with second and fourth moment certificates
-- statement:
--   Fix $0<\alpha\le1$, an integer $\beta\ge2$, and a level $w$ such that
--
--   $$a=\alpha\beta\le10^{-6},\qquad \alpha(w+1)^2>1.$$
--
--   Assume the mission's tight level-$w$ chunk invariant. There are a filtered chunk system $C$ on the next-level space and a real statistic $Z$ on its finite outcome space. Put
--
--   $$s=\sqrt a\,w,\qquad S=\sum_\omega P_\omega\sum_i c_i(\omega).$$
--
--   The weights and requests obey all axioms of the existing chunk-system model, the initial information is constant, every chunk is nonempty, and the nonnegative ceiling $c$, escape price $p$, and Doob jump bound $j$ satisfy
--
--   $$p\le\beta3^w,\qquad c+j\le\frac{11}{8}3^w.$$
--
--   The statistic and the actual total obey
--
--   $$\mathbb E[Z^2]\ge\frac{s^2}{4},\qquad \mathbb E[Z^4]\le4s^4,$$
--
--   $$S\ge\left(3aw^2+\frac12\mathbb E|Z|\right)3^w.$$
--
--   This is an open construction certificate separating the request construction and information bounds from the scalar moment estimate. The total-mass accounting follows the form of equation (3) in BCR's race analysis.
--
--   **Formalization Note** This is a proposed sufficient construction lemma for the platform's tight-escape-price adaptation. The tight escape price, combined ceiling/jump budget, and explicit moment constants are additional proof obligations, not assertions already established by BCR's paper or by this submission. In particular, no Doob-jump bound is inferred merely from the input size window. The second-moment requirement is part of the certificate; it is not claimed for the paper's unmodified stopping rule.
-- source:
--   Bubeck, Coester and Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1 (stages 1–3), Section 4.2, equations (3) and (4), printed pp. 16–19. Proposed moment-certificate adaptation of Claim 13 for platform frontier KServer.bcr_claim13_relative_efficiency. The source proves its original construction using Lemma 14, whereas this open sufficient interface asks explicitly for moment estimates and the existing tight frontier’s price and oscillation budgets; it is not a verbatim theorem from the paper.

import Definitions.Def_KServer_bcr_induction_tight
import Definitions.Def_KServer_chunk_cond
open KServer

theorem KServer.bcr_claim13_race_moment_construction (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β) (hsmall : α * (β : ℝ) ≤ 1 / 10 ^ 6)
    (w : ℕ) (hw : 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2)
    (hC : BCRInductiveChunksTight α β hβ w) :
    ∃ cB jb pe : ℝ, 0 ≤ cB ∧ 0 ≤ jb ∧ 0 ≤ pe ∧
      ∃ C : @ChunkSystemB (bcrLevel2 β hβ (w + 1)).carrier
          (bcrLevel2 β hβ (w + 1)).metric
          (bcrLevel2 β hβ (w + 1)).s (bcrLevel2 β hβ (w + 1)).t
          0 cB 0 pe 0,
        ∃ Z : C.Ω → ℝ,
          (Real.sqrt (α * β) * (w : ℝ)) ^ 2 / 4 ≤ (∑ ω, C.P ω * Z ω ^ 2) ∧
          (∑ ω, C.P ω * Z ω ^ 4) ≤ 4 * (Real.sqrt (α * β) * (w : ℝ)) ^ 4 ∧
          (3 * (α * β) * (w : ℝ) ^ 2 + (∑ ω, C.P ω * |Z ω|) / 2) * 3 ^ w
            ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) ∧
          pe ≤ (β : ℝ) * 3 ^ w ∧
          cB + jb ≤ 11 / 8 * (3 : ℝ) ^ w ∧
          (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) ∧
          (∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) ∧
          C.DoobJumpBound jb := by sorry
