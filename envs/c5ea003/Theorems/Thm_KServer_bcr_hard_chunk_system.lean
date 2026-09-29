-- Prove2me | Theorems.Thm_KServer_bcr_hard_chunk_system
-- name    : KServer.bcr_hard_chunk_system
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-04T22:43:04.741812+00:00
-- url     : https://prove2.me/theorems/f1f3f373-1765-46d0-a994-285e2dccf680
-- title:
--   BCR 2023, Lemma 12 — a chunk system on $k+1$ points with expected total $\\Omega(\\log^2 k)\\,d(s,t)$
-- statement:
--   **A hard chunk system on $k+1$ points: the recursive core of the Bubeck--Coester--Rabani lower bound.**
--
--   Small set chasing (metrical service systems, MSS) asks a single server -- the *evader* -- to move into each of a sequence of requested subsets of a metric space, paying the distance travelled. The Bubeck--Coester--Rabani refutation of the randomized $k$-server conjecture builds, for every $k$, a $(k+1)$-point metric space on which small set chasing has randomized competitive ratio $\Omega(\log^2 k)$.
--
--   The engine of that construction is their Lemma 12: a *chunk system*. Given a metric space with two marked points $s \ne t$, a chunk system is a finitely supported random sequence of $M$ chunks of set requests, adapted to an explicit filtration, together with adapted *sizes* $c_1,\dots,c_M$ such that
--
--   * the last request of the last chunk is $\{t\}$, and an offline server can serve the whole sequence from $s$ for cost at most $d(s,t)$;
--   * conditionally on the history before chunk $i$, **every** deterministic online evader pays at least $c_i$ on chunk $i$ in expectation, even when an escape price is available on that chunk;
--   * the sizes lie in the prescribed window, and the expected total $\sum_i c_i$ is at least $T$.
--
--   This is the structure `ChunkSystemB X s t cLo cHi T price M` of the platform's definition file.
--
--   The statement asserts that there are a constant $c>0$ and a threshold $k_0$ such that for every $k \ge k_0$ one can put a metric on the $(k+1)$-point set, choose two points $s \ne t$ in it, and construct a chunk system between them (with size floor $0$, some ceiling, some nonnegative escape price and some number of chunks) whose expected total satisfies
--   $$T \;\ge\; c\,(\log k)^2\, d(s,t).$$
--
--   In other words: a single run of the instance forces every online evader to pay $\Omega(\log^2 k)$ times what the offline optimum pays, on a space of only $k+1$ points.
--
--   **Why this is the remaining gap.** Together with the standard repetition argument -- concatenating independent runs, each followed by a request $\{s\}$ that forces the evader back to the start -- this lemma yields the full distributional (Yao-form) statement of BCR's Theorem 11, `KServer.mss_randomized_lower_bound`, and hence the $\Omega(\log^2 k)$ randomized $k$-server lower bound. That derivation is already machine-checked on the platform; what remains is the construction stated here.
--
--   **Formalization note.** The metric is existentially quantified as a `MetricSpace (Fin (k+1))` instance, so the carrier has exactly $k+1$ points; a construction on fewer points must be padded (for instance by clones at a tiny distance) to reach exactly $k+1$. The size floor is fixed to $0$ while the ceiling, the escape price and the number of chunks are existential, since only the expected total matters downstream. Distances are unnormalized: the bound is the scale-invariant ratio $T/d(s,t)$.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, https://arxiv.org/abs/2211.05753, Section 4, Lemma 12 (random sequence of chunks with sizes c_i, expected total at least alpha w^2 d(s_w,t_w) on the space M_w with |M_w| <= beta*6^w), packaged as the platform structure ChunkSystemB and instantiated on a (k+1)-point space with w = Theta(log k).

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

theorem bcr_hard_chunk_system :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ (m : MetricSpace (Fin (k + 1))) (s t : Fin (k + 1)) (cHi T price : ℝ) (M : ℕ),
        0 ≤ price ∧
        0 < @dist (Fin (k + 1)) m.toDist s t ∧
        c * Real.log k ^ 2 * @dist (Fin (k + 1)) m.toDist s t ≤ T ∧
        Nonempty (@ChunkSystemB (Fin (k + 1)) m s t 0 cHi T price M) := by sorry

end KServer
