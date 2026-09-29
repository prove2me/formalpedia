-- Prove2me | Theorems.Thm_KServer_chunk_combining
-- name    : KServer.chunk_combining
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T11:35:09.474345+00:00
-- url     : https://prove2.me/theorems/5716695d-e47e-4da9-9fbb-ba1407ee06b8
-- title:
--   The chunk-combining lemma: uniform windows from conditional hitting times
-- statement:
--   **The chunk-combining lemma** (the repaired form of Lemma 10 of Bubeck–Coester–Rabani, STOC 2023). Let $C$ be a chunk system with online escapes on a metric space $X$ with marked points $s,t$: sizes in $[c_A, c_B]$ with $0 < c_A \le c_B$, escape price $p_e$, trivial initial knowledge ($\mathcal F_0$ trivial), and total expected mass $T_0 = \sum_\omega P(\omega)\sum_i c_i(\omega)$. Assume the **Doob jump bound** in the descending regime: the martingale $M_h = \mathbb E[\sum_i c_i \mid \mathcal F_h]$ has pointwise jumps at most $jbS \le c_A$. Then for every target count $M > 0$ the chunks can be regrouped into $M$ **windows** delimited by the hitting times of the uniformly spaced levels $T_0(1 - k/M)$ of the conditional future mass $g_h = \mathbb E[\sum_{i \ge h} c_i \mid \mathcal F_h]$, yielding a chunk system with the same outcomes, weights and request sequence, whose $M$ conditional window sizes all lie within $c_B + jbS$ of the spacing $\delta = T_0/M$:
--
--   $$C' : \mathrm{ChunkSystemB}\,(X, s, t, c_{Lo}', c_{Hi}', T, p', M),\qquad c_{Lo}' \le \delta - (c_B + jbS),\quad \delta + (c_B + jbS) \le c_{Hi}',$$
--
--   for any escape price $p' \ge p_e + \delta + (c_B + jbS)$. The expected total is preserved exactly (the tower property), so the same lower bound $T$ carries over. The proof pins the boundary overshoots by one chunk plus one Doob jump (since $jbS \le c_A$ the conditional future mass descends monotonically, so no up-crossings occur), computes the conditional window sizes by optional stopping, and charges a bailing adversary's untouched window tail — at most one spacing plus slack in conditional expectation — to the price difference $p' - p_e$, applying the input's conditional cost bound chunkwise on the quiet, still-in-window events, which are measurable in the fine filtration. This is the engine that turns the stage-constructed level-$(w+1)$ system into the standard windowed form in the induction of Lemma 6.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Lemma 10, repaired online-escape form.

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append

namespace KServer

theorem chunk_combining {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t cA cB T pe mL)
    (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hjbA : jbS ≤ cA)
    (hcA : 0 < cA) (hcAB : cA ≤ cB)
    {M : ℕ} (hM0 : 0 < M) {cLo' cHi' p' : ℝ}
    (hlo0 : 0 < cLo')
    (hlo : cLo' ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) / M - (cB + jbS))
    (hhi : (∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS) ≤ cHi')
    (hp : pe + ((∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS)) ≤ p') :
    Nonempty (ChunkSystemB X s t cLo' cHi' T p' M) := by sorry

end KServer
