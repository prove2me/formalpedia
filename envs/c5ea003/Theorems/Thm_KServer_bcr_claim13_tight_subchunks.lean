-- Prove2me | Theorems.Thm_KServer_bcr_claim13_tight_subchunks
-- name    : KServer.bcr_claim13_tight_subchunks
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-10T11:07:16.601051+00:00
-- url     : https://prove2.me/theorems/ca0ddc25-0e50-46ef-ae99-09f2b983730f
-- title:
--   BCR Claim 13: the subchunk system of one level, at the tight escape price
-- statement:
--   **Claim 13 of Bubeck--Coester--Rabani, in the form the regrouping of Lemma 15 consumes.**
--
--   Let $\mathcal M_w=\mathtt{bcrLevel2}\ \beta\ w$ be the level-$w$ space of the recursive BCR family, with marked points $s_w,t_w$ at distance $d_w=\beta 3^w$, and let $\mathrm{ChunksTight}(\alpha,\beta,w)$ be the level invariant `KServer.BCRInductiveChunksTight`: a chunk system with online escapes on $\mathcal M_w$ with sizes in $[3^w/2,\,3\cdot 3^w/2]$, expected total at least $\alpha\beta w^2 3^w$, escape price $d_w$, exactly $M\ge\lceil\alpha\beta w^2\rceil$ chunks, constant initial information and no empty chunk.
--
--   **Statement.** Fix constants $0<\alpha\le 1$ and an integer $\beta\ge 2$ subject to the smallness relation $\alpha\beta\le 10^{-6}$, and let $w$ be a level with $\alpha(w+1)^2>1$. If $\mathrm{ChunksTight}(\alpha,\beta,w)$ holds, then on the next level's space $\mathcal M_{w+1}$ there are reals $c_B,j\ge 0$ with
--   $$c_B+j\ \le\ \tfrac{11}{8}\,3^{w},$$
--   and a chunk system with online escapes between $s_{w+1}$ and $t_{w+1}$ whose
--
--   * size floor is $0$ and whose size ceiling is $c_B$;
--   * escape price is $d_w=\beta 3^w$, unchanged from level $w$;
--   * Doob martingale of the total mass has one-step jumps at most $j$;
--   * expected total mass is exactly $\alpha\beta(w+1)^2\,3^{w+1}$;
--   * initial information is constant, and no chunk is empty.
--
--   **Content.** This is the first half of one level of BCR's Lemma 12, namely Claim 13: the three-stage construction of subchunks on the six-copy next-level space --- stage 1, the stage-2a race with its anti-concentration gain, stage 2b and stage 3. Stages 1, 2b and 3 contribute three copies of the level-$w$ mass, so the mass triples while the distance triples too; the race must contribute the further $\Theta(\alpha\beta w)$ chunk masses that raise the competitive ratio from $\alpha\beta w^2$ to $\alpha\beta(w+1)^2$. That is what the smallness relation $\alpha\beta\le 10^{-6}$ is for: the anti-concentration gain of a race of $\kappa\le M\approx\alpha\beta w^2$ steps with chunk masses of order $3^w$ is of order $\sqrt{\kappa}\,3^w\approx\sqrt{\alpha\beta}\,w\,3^w$, which dominates the required increment $\approx 6\alpha\beta w\,3^w$ exactly when $\sqrt{\alpha\beta}$ is small enough.
--
--   Two features of the conclusion are normalisations rather than content. Fixing the expected total *exactly* at the level-$(w+1)$ target $\alpha\beta(w+1)^2 3^{w+1}$ is free once at least that much mass has been produced, because the sizes of a chunk system may always be scaled down: every hypothesis of `KServer.ChunkSystemB` is monotone in the sizes. And bounding the ceiling plus the Doob jump by $\frac{11}{8}3^w$ is precisely the budget that the regrouping needs: the level-$(w+1)$ window $[3^{w+1}/2,\ 3\cdot 3^{w+1}/2]$ is centred at $3^{w+1}$ with half-width $3^{w+1}/2=\frac32\,3^{w}$, and a regrouping into $\lceil\alpha\beta(w+1)^2\rceil$ chunks of mean mass $3^{w+1}$ spends $c_B+j$ of that half-width on each side, plus a further $3^{w+1}/\lceil\alpha\beta(w+1)^2\rceil$ for the integrality of the chunk count; $c_B+j\le\frac{11}{8}3^{w}$ leaves both affordable as soon as $\alpha\beta(w+1)^2\ge 64$.
--
--   **Why this formulation.** Together with the zero-floor regrouping `KServer.chunk_combining_zero_floor` this statement gives one full level of the induction: regrouping the subchunk system into $\lceil\alpha\beta(w+1)^2\rceil$ chunks of mean mass $3^{w+1}$ puts the sizes inside the level-$(w+1)$ window, raises the escape price from $\beta 3^w$ to at most $\beta 3^{w+1}$, and preserves the total, the constant initial information and the nonemptiness of the chunks --- which is exactly $\mathrm{ChunksTight}(\alpha,\beta,w+1)$.
--
--   **What remains for a prover.** The parameter schedule of the race inside Claim 13: the number of coin steps $\kappa$, the tie-break scale $\varepsilon$, the floor used in the anti-concentration bound and the depth of the sturdiness invariant, subject to the gain of `KServer.level_step_sturdy` exceeding the losses it charges. Note that the level invariant supplies the sturdiness, Doob-jump and variance hypotheses of that step only through the crude window bounds of `KServer.chunk_window_invariants` and `KServer.chunk_window_variance`, whose defect $m\,(c_{Hi}-c_{Lo})$ is of the same order as the whole mass; sharpening that, or carrying a regularity invariant through the construction, is the substance of the claim.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753: Claim 13 (pp. 15-19), the induction step of Lemma 12 (p. 14), stated over the platform predicate KServer.BCRInductiveChunksTight and with the slack budget required by Lemma 15 (pp. 19-21).

import Mathlib
import Definitions.Def_KServer_bcr_induction_tight
import Definitions.Def_KServer_chunk_cond

namespace KServer

theorem bcr_claim13_tight_subchunks (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β) (hsmall : α * (β : ℝ) ≤ 1 / 10 ^ 6)
    (w : ℕ) (hw : 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2)
    (hC : BCRInductiveChunksTight α β hβ w) :
    ∃ cB jbS : ℝ, 0 ≤ cB ∧ 0 ≤ jbS ∧ cB + jbS ≤ 11 / 8 * (3 : ℝ) ^ w ∧
      ∃ C : @ChunkSystemB (bcrLevel2 β hβ (w + 1)).carrier
          (bcrLevel2 β hβ (w + 1)).metric
          (bcrLevel2 β hβ (w + 1)).s (bcrLevel2 β hβ (w + 1)).t
          0 cB ((α * β * ((w + 1 : ℕ) : ℝ) ^ 2) * 3 ^ (w + 1)) ((β : ℝ) * 3 ^ w) 0,
        (∑ ω, C.P ω * ∑ i, C.size ω i)
            = (α * β * ((w + 1 : ℕ) : ℝ) ^ 2) * 3 ^ (w + 1) ∧
        (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) ∧
        (∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) ∧
        C.DoobJumpBound jbS := by sorry

end KServer
