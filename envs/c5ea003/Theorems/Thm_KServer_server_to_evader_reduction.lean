-- Prove2me | Theorems.Thm_KServer_server_to_evader_reduction
-- name    : KServer.server_to_evader_reduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T08:46:44.107189+00:00
-- url     : https://prove2.me/theorems/e028d6fd-3043-43ba-8e64-b95debd18c66
-- title:
--   The k-server to evader reduction on k+1 points (online direction)
-- statement:
--   Let $M$ be a metric space with exactly $k+1$ points, with minimum positive distance $\delta$ and diameter at most $\Delta$, and let $R$ satisfy $\Delta \le R\delta$. From every **lazy simple** deterministic $k$-server algorithm $\mathcal{B}$ on $M$ (injective configurations, no motion on covered requests, single-server moves — as supplied by `exists_lazy_injective_algorithm`) one can extract a deterministic evader (MSS) algorithm $\mathcal{E}$ starting at the hole of $\mathcal{B}$'s initial configuration, with
--
--   $$c_{\mathcal{E}}(\sigma) \;\le\; 4\, c_{\mathcal{B}}(\mathrm{enc}_R(\sigma)) \qquad \text{for every set-request sequence } \sigma,$$
--
--   where $\mathrm{enc}_R$ encodes each set request $S$ as $R$ passes through $M \setminus S$.
--
--   ## Role
--
--   This is the online half of the folklore reduction $C^{k\text{-}\mathrm{SRV}}(\mathcal{M}) \ge C^{\mathrm{MSS}}(\mathcal{M})$ for $(k+1)$-point spaces (Bubeck–Coester–Rabani, STOC 2023, Proposition 2.6): a lower bound against every deterministic evader algorithm transfers, through this theorem, to a lower bound against every deterministic $k$-server algorithm on the encoded sequences — the key step in carrying the $\Omega(\log^2 k)$ construction from MSS to the $k$-server problem.
--
--   ## Proof idea
--
--   A lazy simple configuration on $k+1$ points leaves exactly one *hole* uncovered. Requests away from the hole are covered and free; a request at the hole moves it, at a cost equal to its displacement. Hence during one pass through $M \setminus S$ a hole outside $S$ is necessarily hit (it cannot move until its own point is requested), paying at least $\delta$; once the hole enters $S$ it is never touched again by the block. After $R$ passes the hole is in $S$, or the block has paid $R\delta \ge \Delta$ — enough to pay for teleporting the evader into $S$. The evader is therefore defined as the hole, adjusted into the last requested set when necessary; its per-block movement is at most the hole's displacement (dominated by the block cost) plus two adjustments (each dominated by the cost of the block that caused them), giving the factor $4$.
--
--   ## Formalization note
--
--   The hole is the unique point outside the configuration's range, by a counting argument; the potential in the induction is the evader cost plus twice the standing adjustment distance.
-- source:
--   Folklore; S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Proposition 2.6, online direction.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_encoding

namespace KServer

theorem server_to_evader_reduction (k : ℕ) (M : Type*) [MetricSpace M] [Fintype M]
    (hcard : Fintype.card M = k + 1)
    (δ Δ : ℝ) (hδ0 : 0 < δ) (hδ : ∀ x y : M, x ≠ y → δ ≤ dist x y)
    (hΔ : ∀ x y : M, dist x y ≤ Δ) (R : ℕ) (hR : Δ ≤ R * δ)
    (B : OnlineAlgorithm k M)
    (hBinj : ∀ l : List M, Function.Injective (B.conf l))
    (hlazy : ∀ (l : List M) (r : M), (∃ i, B.conf l i = r) → B.conf (l ++ [r]) = B.conf l)
    (hlazy2 : ∀ (l : List M) (r : M), ∃ i : Fin k,
      B.conf (l ++ [r]) = Function.update (B.conf l) i r) :
    ∃ E : EvaderAlgorithm M,
      (E.pos [] ∉ Set.range (B.conf [])) ∧
      ∀ σ : List (Set M), E.cost σ ≤ 4 * B.cost (encSeq M R σ) := by sorry

end KServer
