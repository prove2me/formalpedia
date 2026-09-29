-- Prove2me | Theorems.Thm_KServer_bcr_tight_step
-- name    : KServer.bcr_tight_step
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-07T21:28:02.75016+00:00
-- url     : https://prove2.me/theorems/cb47fce0-1867-4c62-8847-9bc1b0b1d04e
-- title:
--   One level of BCR Lemma 12 at the tight escape price
-- statement:
--   Let $\mathrm{ChunksTight}(\alpha,\beta,w)$ be the level invariant of `KServer.BCRInductiveChunksTight`: on the level-$w$ space $\mathcal M_w$ of the recursive Bubeck--Coester--Rabani family, a chunk system between the marked points $s_w,t_w$ (at distance $d_w=\beta 3^w$) with sizes in $[3^w/2,\,3\cdot3^w/2]$, expected total at least $\alpha\beta w^2 3^w$, escape price $d_w$, exactly $M\ge\lceil\alpha\beta w^2\rceil$ chunks, constant initial information and no empty chunk.
--
--   **Statement.** There are constants $0<\alpha\le1$ and an integer $\beta\ge2$, chosen once and for all, such that for every level $w$ with $\alpha(w+1)^2>1$,
--   $$\mathrm{ChunksTight}(\alpha,\beta,w)\ \Longrightarrow\ \mathrm{ChunksTight}(\alpha,\beta,w+1).$$
--
--   **Content.** This is one full level of the induction of BCR's Lemma 12: Claim 13, which builds subchunks on the six-copy next-level space out of the level-$w$ system in three stages and extracts the anti-concentration gain of the stage-2a race, followed by the regrouping of Lemma 15, which merges the subchunks into chunks of the next scale and restores the size window and the chunk count. The competitive ratio must rise from $\alpha\beta w^2$ to $\alpha\beta(w+1)^2$ while the distance triples, so the race has to contribute $\Theta(\alpha\beta w)$ chunk masses beyond the three copies supplied by stages 1, 2b and 3; this is what forces $\sqrt{\alpha\beta}\lesssim1$ and fixes the relation between the two constants.
--
--   **Why this formulation.** Every hypothesis of the proved level step `KServer.level_step_sturdy` is available from the invariant. Its taut-space hypothesis is `KServer.bcrLevel2_taut`. Its variance, sturdiness, Doob-jump and below-floor-count hypotheses follow from the two-sided size window through `KServer.chunk_window_variance` and `KServer.chunk_window_invariants`, with the below-floor count equal to zero for any floor at most $3^w/2$. The exact chunk count and the nonemptiness of the chunks are carried by the invariant. And, decisively, the escape price is $d_w$ rather than $2d_w$, which is what the step's hypothesis `p ≤ dist s t` demands; the older predicate `KServer.BCRInductiveChunks` fails this, and no adjustment can repair it, because the cost bound of a chunk system is stated against its escape price and `KServer.ChunkSystemB.adjust` can only raise it. The step's output price may be any value at least the input's, so the invariant's price $d_{w+1}=3d_w$ is reachable.
--
--   **What remains for a prover.** The choice of the parameter schedule: the number of coin steps $\kappa$, the tie-break scale $\varepsilon$, the floor used in the anti-concentration bound, and the block length of the regrouping, subject to the gain of `KServer.level_step_sturdy` exceeding the losses it charges. The regrouping is `KServer.chunk_combining_strong`, which returns exactly the three structural clauses of the invariant.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753: Lemma 12 (p. 14) with its base case (p. 15, the levels with alpha w^2 <= 1) and its induction step (Claim 13, p. 15-19, and Lemma 15, p. 19-21). Stated over the platform predicate KServer.BCRInductiveChunksTight, whose escape price d_w matches the hypotheses of KServer.level_step_sturdy.

import Definitions.Def_KServer_bcr_induction_tight

namespace KServer

theorem bcr_tight_step :
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧ ∃ β : ℕ, ∃ hβ : 0 < β, 2 ≤ β ∧
      ∀ w : ℕ, 1 < α * ((w + 1 : ℕ) : ℝ) ^ 2 →
        BCRInductiveChunksTight α β hβ w →
        BCRInductiveChunksTight α β hβ (w + 1) := by sorry

end KServer
