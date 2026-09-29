-- Prove2me | Theorems.Thm_KServer_bcr_tight_base
-- name    : KServer.bcr_tight_base
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T21:27:48.313083+00:00
-- url     : https://prove2.me/theorems/45801152-eb51-4de6-a772-f47f9109d06f
-- title:
--   Base case of BCR Lemma 12 at the tight escape price
-- statement:
--   Let $\mathcal M_w$ be the level-$w$ member of the recursive Bubeck--Coester--Rabani space family, with marked points $s_w,t_w$ at distance $d_w=\beta\,3^w$, and let $\mathrm{ChunksTight}(\alpha,\beta,w)$ be the level invariant of `KServer.BCRInductiveChunksTight`: a chunk system on $\mathcal M_w$ with sizes in $[3^w/2,\,3\cdot3^w/2]$, expected total at least $\alpha\beta w^2 3^w$, escape price $d_w$, exactly $M\ge\lceil\alpha\beta w^2\rceil$ chunks, constant initial information and no empty chunk.
--
--   **Statement.** For every $\alpha\ge0$, every integer $\beta\ge2$ and every level $w$ with
--   $$\alpha w^2\;\le\;1,$$
--   the invariant $\mathrm{ChunksTight}(\alpha,\beta,w)$ holds.
--
--   **Why this is the easy half.** When $\alpha w^2\le1$ the demanded expected total $\alpha\beta w^2 3^w$ is at most $\beta 3^w=d_w$, so no randomness is needed: a deterministic single-file adversary suffices. Level $w$ of the family contains a unit geodesic chain $g$ with $g(0)=s_w$, $g(\beta 3^w)=t_w$ and $d(g(i),g(j))=|i-j|$; sampling it at the multiples of $3^w$ gives $\beta+1$ marked positions at spacing $3^w$, and the singleton requests at those positions, one per chunk, form a chunk system of $\beta$ chunks of size $3^w$. Each chunk forces the evader to advance one step of the chain, and bailing out is never cheaper because the escape price $\beta3^w$ is at least the chunk size $3^w$.
--
--   **Relation to the existing base case.** This is `KServer.bcr_induction_base` with the escape price lowered from $2d_w$ to $d_w$ and with the two structural clauses that the level steps additionally require: the exact chunk count and nonemptiness of the chunks. The lower price is what makes the invariant chainable, since `KServer.level_step_sturdy` assumes its input price is at most $d(s,t)$, and it costs nothing here: the cost bound of the single-file system holds against any escape price at least the chunk size. The geodesic chain in the glued family and the single-file system along an arbitrary chain are the two ingredients of the existing proof and can be reused verbatim.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753: Lemma 12 (p. 14) with its base case (p. 15, the levels with alpha w^2 <= 1) and its induction step (Claim 13, p. 15-19, and Lemma 15, p. 19-21). Stated over the platform predicate KServer.BCRInductiveChunksTight, whose escape price d_w matches the hypotheses of KServer.level_step_sturdy.

import Definitions.Def_KServer_bcr_induction_tight

namespace KServer

theorem bcr_tight_base (α : ℝ) (hα : 0 ≤ α) (β : ℕ) (hβ : 0 < β) (hβ2 : 2 ≤ β)
    (w : ℕ) (hw : α * (w : ℝ) ^ 2 ≤ 1) :
    BCRInductiveChunksTight α β hβ w := by sorry

end KServer
