-- Prove2me | Theorems.Thm_KServer_slow_decrement_of_doob_jump
-- name    : KServer.slow_decrement_of_doob_jump
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-07T23:13:03.30164+00:00
-- url     : https://prove2.me/theorems/ae18ee64-7d79-4eb4-899c-f3b91fb92ec2
-- title:
--   A pointwise Doob jump bound implies slow decrement
-- statement:
--   Let $C$ be a chunk system with online escapes, with adapted sizes $c_j$ confined to $[c_{\mathrm{Lo}},c_{\mathrm{Hi}}]$ and filtration $(\mathcal F_h)$. Write
--   $$\Sigma=\sum_j c_j,\qquad D_h=\mathbb E[\Sigma\mid\mathcal F_h],\qquad F_h=\mathbb E\Bigl[\sum_{j\ge h}c_j\ \Bigm|\ \mathcal F_h\Bigr].$$
--   $D$ is the Doob martingale of the total and $F$ the conditional expected remaining size. A **Doob jump bound** $jb$ asserts $|D_{h+1}-D_h|\le jb$ in every branch and at every time; **slow decrement** with parameter $c_{\max}$ asserts $F_h-c_{\max}\le F_{h+1}$ in every branch and at every time.
--
--   **Statement.** If $C$ has a Doob jump bound $jb$ and $c_{\mathrm{Hi}}\ge0$, then $C$ satisfies slow decrement with parameter $c_{\mathrm{Hi}}+jb$.
--
--   **Why it matters.** Slow decrement is the hypothesis that repairs the regrouping step of Bubeck--Coester--Rabani's Lemma 15, whose published proof derives the pointwise bound of its property 4 from a claim that holds only in conditional expectation; the platform records this in `KServer.chunk_regroup_stable`, which assumes it. The statement here says that slow decrement is not an extra assumption at all once a pointwise Doob jump bound is available: since the sizes are adapted, the past mass $\Sigma-\sum_{j\ge h}c_j$ is known at time $h$, so
--   $$F_h=D_h-\sum_{j<h}c_j,\qquad F_h-F_{h+1}=(D_h-D_{h+1})+c_h\;\le\;jb+c_{\mathrm{Hi}} .$$
--   A single revealed chunk moves the remaining mass by its own size plus one jump of the Doob martingale, and nothing else.
--
--   This matters for the recursion of the $\Omega(\log^2 k)$ lower bound because a Doob jump bound is a hypothesis the constructions can actually meet, whereas the companion hypothesis of `KServer.chunk_regroup_stable`, bounded surprise, cannot be met by any construction whose total carries a random fluctuation larger than one chunk: bounded surprise with slack $c_{\max}$ forces every branch total to be within $c_{\max}$ of the mean, which is `KServer.bounded_surprise_total_le`.
--
--   **Formalization note.** The conclusion is stated over `KServer.ChunkSystemB.SlowDecrementC` of `Def_KServer_chunk_slow_decrement_cond`, which phrases slow decrement over the conditional expectation `condFuture` of `Def_KServer_chunk_cond`. The older `KServer.ChunkSystemB.SlowDecrement` is phrased over a second copy of the atom map declared in `Def_KServer_chunk_slow_decrement`; because the two copies carry the same fully qualified name, no Lean file can import that file together with `Def_KServer_chunk_cond`, and the latter is a dependency of the level steps, the regrouping combinators and the window lemmas.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The randomized k-server conjecture is false!, STOC 2023, https://arxiv.org/abs/2211.05753, Lemma 15 (pp. 19-21), property 4 and its proof. The implication itself is an elementary identity for the Doob martingale of the total size of a chunk system.

import Mathlib
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_slow_decrement_cond

namespace KServer

theorem slow_decrement_of_doob_jump {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mLo) {jb : ℝ}
    (hjb : C.DoobJumpBound jb) (hcHi : 0 ≤ cHi) :
    C.SlowDecrementC (cHi + jb) := by sorry

end KServer
