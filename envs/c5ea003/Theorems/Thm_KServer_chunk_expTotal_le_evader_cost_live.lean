-- Prove2me | Theorems.Thm_KServer_chunk_expTotal_le_evader_cost_live
-- name    : KServer.chunk_expTotal_le_evader_cost_live
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T01:18:48.544091+00:00
-- url     : https://prove2.me/theorems/dd3c9ee4-2aa6-4cb0-adf9-263a9403918c
-- title:
--   A chunk system's expected total size is paid for by every evader's cost on the flattened chunk list
-- statement:
--   Fix a metric space $X$ with marked points $s,t$, and a chunk system $C$: a finitely supported random sequence of $m$ chunks of set requests, with sizes $c_1,\dots,c_m$, an explicit refining filtration, strictly positive outcome weights $P$ summing to $1$, and a conditional cost axiom stating that for every chunk index $i$, every outcome $\omega_0$, every online evader $E$ and every escape rule, the size $c_i(\omega_0)$ is bounded by the escape-relaxed cost of serving chunk $i$ after the flattened prefix of the chunks before it. Let $E$ be any online algorithm for the resulting small set chasing (metrical service systems) problem, and let $\mathrm{seq}\,\omega$ be the concatenation of all the chunks of outcome $\omega$ into a single request sequence.
--
--   **Statement.** The expected total size of the chunk system is at most the $P$-weighted cost of $E$ on the flattened sequence:
--   $$\mathbb{E}_{\omega}\Bigl[\sum_{i} c_i(\omega)\Bigr] \;\le\; \mathbb{E}_{\omega}\bigl[\mathrm{cost}\,E\,(\mathrm{seq}\,\omega)\bigr].$$
--
--   **Role.** This is the bridge that connects the *chunk-system* world of BCR's induction to the *cost* world in which a lower bound is eventually handed to the $k$-server problem, and it is the step that turns a purely combinatorial induction package into a statement about movement cost. It is what bounds the total mass a chunk system may declare, since `total` is a lower bound for the expected total size in the definition of `ChunkSystemB`. Without it the quantity `total` is unconstrained by any geometric fact, and the size axioms alone do not produce a genuine lower bound.
--
--   **Why it is provable without any regularity hypothesis.** Instantiate the conditional cost axiom with the escape rule that never fires, so that the escape-relaxed cost reduces to the evader's honest cost of serving that chunk after the flattened prefix of the preceding chunks; sum the resulting inequalities over the chunk indices, and then take the $P$-weighted sum over outcomes. Because the chunks of an outcome are served consecutively, the partial costs of the individual chunks tile the cost of the whole flattened sequence, and the weights on the left are exactly the same weights. No branchwise (pointwise) regularity is required, which is why the statement is about the *expected* total size, matching the expected cost on the right.
--
--   This is a live-revision restatement of the charging lemma; the identical statement was previously established on an earlier revision of the environment, where it was accompanied by auxiliary saturation and conditional-expectation machinery that is not required here.
-- source:
--   Bubeck, Coester, and Rabani, Lower Bounds for the $k$-Server Problem (STOC 2023), the charging argument of their Lemma 6: the expected total chunk size is bounded by the cost of any evader on the induced request sequence. Restated for the ChunkSystemB formalization of the BCR induction; see also Manasse--McGeoch--Sleator, Competitive Algorithms for Server Problems, J. Algorithms 11 (1990) 208-230, for the small set chasing (metrical service systems) cost model.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

/-- The expected total size of a chunk system is at most the cost of any evader
algorithm on the flattened request sequence of any outcome, averaged over the
outcome distribution. This is the charging argument of BCR's Lemma 6, restated
for the `ChunkSystemB` formalization: each chunk's size is charged to the evader
by the conditional cost axiom, and the chunks of an outcome are served
consecutively, so the per-chunk partial costs tile the cost of the whole
flattened sequence. -/
theorem chunk_expTotal_le_evader_cost_live {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cLo cHi total price mL)
    (E : EvaderAlgorithm X) :
    (∑ ω, C.P ω * ∑ i, C.size ω i) ≤
      ∑ ω, C.P ω * E.cost (C.seq ω) := by sorry

end KServer
