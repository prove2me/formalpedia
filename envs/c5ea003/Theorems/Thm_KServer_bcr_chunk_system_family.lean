-- Prove2me | Theorems.Thm_KServer_bcr_chunk_system_family
-- name    : KServer.bcr_chunk_system_family
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-04T23:09:19.290494+00:00
-- url     : https://prove2.me/theorems/e4a71277-9282-49cc-bffe-db36a79d0525
-- title:
--   BCR 2023, Lemma 12 — chunk systems of ratio $\\Omega(\\log^2 k)$ on at most $k+1$ points
-- statement:
--   **The recursive core of the Bubeck--Coester--Rabani lower bound, on spaces of at most $k+1$ points.**
--
--   Small set chasing (metrical service systems) asks a single server -- the *evader* -- to move into each of a sequence of requested subsets of a metric space, paying the distance travelled. Bubeck--Coester--Rabani prove that there are $n$-point metric spaces on which small set chasing has randomized competitive ratio $\Omega(\log^2 n)$, refuting the randomized $k$-server conjecture. The engine of their proof is a recursively constructed *chunk system* (their Lemma 12).
--
--   A chunk system `ChunkSystemB X s t cLo cHi T price M` between two marked points $s,t$ of a metric space $X$ consists of a finitely supported random sequence of $M$ chunks of set requests, adapted to an explicit filtration, together with adapted sizes lying in $[c_{Lo},c_{Hi}]$, such that the last request is $\{t\}$, an offline server starting at $s$ serves everything for at most $d(s,t)$, the expected total of the sizes is at least $T$, and, conditionally on the history, every deterministic online evader pays at least the size of the current chunk on that chunk -- even if it may escape the chunk for a one-time price.
--
--   The statement asserts that there are a constant $c>0$ and a threshold $k_0$ such that for every $k \ge k_0$ there is a **finite metric space $X$ with at most $k+1$ points**, two points $s \ne t$ of it, and a chunk system between them with size floor $0$, trivial initial history and nonnegative escape price whose expected total obeys
--   $$T \;\ge\; c\,(\log k)^2\, d(s,t).$$
--
--   **Role.** Padding such a space to exactly $k+1$ points (`KServer.chunk_system_pad`) and then repeating the instance yields the distributional $\Omega(\log^2 k)$ lower bound for small set chasing on $(k+1)$-point spaces, `KServer.mss_randomized_lower_bound`, and hence the $\Omega(\log^2 k)$ randomized $k$-server lower bound. Both of those derivations are already machine-checked on the platform, so this statement is what remains of the refutation.
--
--   **Formalization note.** The carrier is existentially quantified as a bare `Type` together with its `MetricSpace` and `Fintype` instances, with the cardinality bound $|X| \le k+1$ stated separately, so that a construction is free to build whatever space the recursion produces. The size ceiling, escape price and number of chunks are existential, since only the ratio between the expected total and $d(s,t)$ matters downstream. Triviality of the initial history is required because the platform's level-step and mapping combinators both assume and preserve it.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, https://arxiv.org/abs/2211.05753, Section 4, Lemma 12 (for every w a random sequence of chunks in M_w with sizes c_i and expected total at least alpha w^2 d_w(s_w,t_w), where |M_w| <= beta*6^w), stated for w = Theta(log k) so that the space has at most k+1 points.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

theorem bcr_chunk_system_family :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ (X : Type) (mX : MetricSpace X) (fX : Fintype X) (s t : X),
        @Fintype.card X fX ≤ k + 1 ∧
        0 < @dist X mX.toDist s t ∧
        ∃ (cHi T price : ℝ) (M : ℕ) (C : @ChunkSystemB X mX s t 0 cHi T price M),
          0 ≤ price ∧
          c * Real.log k ^ 2 * @dist X mX.toDist s t ≤ T ∧
          (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) := by sorry

end KServer
