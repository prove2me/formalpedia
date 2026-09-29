-- Prove2me | Theorems.Thm_KServer_bcr_level_family
-- name    : KServer.bcr_level_family
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-05T13:08:23.309742+00:00
-- url     : https://prove2.me/theorems/72eb91e9-44df-4633-b275-2db3e28fef8d
-- title:
--   BCR 2023, Lemma 12 — chunk systems of ratio $\alpha w^2$ at every level $w$
-- statement:
--   **Bubeck--Coester--Rabani, Lemma 12: the recursive family of chunk systems.**
--
--   Small set chasing (metrical service systems) asks a single server -- the *evader* -- to move into each of a sequence of requested subsets of a metric space, paying the distance travelled. Bubeck, Coester and Rabani build, by recursion on a level parameter $w$, a family of finite metric spaces $M_w$ with marked points $s_w \ne t_w$ carrying random request sequences against which every online evader must pay $\Omega(w^2)$ times the offline optimum. The bookkeeping device for the recursion is a *chunk system*.
--
--   A chunk system `ChunkSystemB X s t cLo cHi T price M` between two marked points $s,t$ of a metric space $X$ consists of a finitely supported random sequence of $M$ chunks of set requests, adapted to an explicit filtration, together with adapted sizes lying in $[c_{Lo},c_{Hi}]$, such that the last request is $\{t\}$, an offline server starting at $s$ serves the whole sequence for at most $d(s,t)$, the expected total of the sizes is at least $T$, and, conditionally on the history, every deterministic online evader pays at least the size of the current chunk while serving that chunk -- even if it is allowed to escape the chunk for a one-time price.
--
--   The statement asserts that there are a constant $\alpha > 0$ and a base $\beta \ge 1$ such that for **every** level $w$ there is a finite metric space with
--
--   $$|M_w| \;\le\; (\beta+1)\,6^{w}, \qquad d(s_w,t_w) \;=\; \beta\,3^{w},$$
--
--   carrying a chunk system between $s_w$ and $t_w$, with size floor $0$, nonnegative escape price and trivial initial history, whose expected total obeys
--
--   $$T_w \;\ge\; \alpha\, w^{2}\, d(s_w,t_w).$$
--
--   The two numerical constraints are exactly those of the paper's construction: each level replaces the space by a theta gluing of two three-copy chains, which multiplies the number of points by at most $6$ and the distance between the marked points by exactly $3$. The ratio $T_w/d(s_w,t_w)$ therefore grows like the square of the level, i.e. like the square of the logarithm of the number of points.
--
--   **Role.** Together with the level-to-cardinality packaging already verified on the platform, this yields `KServer.bcr_chunk_system_family` (chunk systems of ratio $\Omega(\log^2 k)$ on at most $k+1$ points), hence `KServer.bcr_hard_chunk_system`, hence the small set chasing lower bound `KServer.mss_randomized_lower_bound`, and finally the $\Omega(\log^2 k)$ randomized $k$-server lower bound. All of those derivations are machine-checked, so this statement is what remains of the refutation of the randomized $k$-server conjecture.
--
--   **Formalization note.** The carrier is existentially quantified as a bare `Type` with its `MetricSpace` and `Fintype` instances, and the cardinality and distance constraints are stated separately, so a construction is free to produce whatever space the recursion builds -- for instance the platform's `bcrLevel2` family, whose cardinality and distance bounds are already proved. The size ceiling, escape price and number of chunks are existential, since only the ratio between the expected total and $d(s,t)$ matters downstream. Triviality of the initial history is required because the platform's level-step and mapping combinators both assume and preserve it.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, https://arxiv.org/abs/2211.05753, Section 4, Lemma 12 (for every w a random sequence of chunks in M_w with sizes c_i and expected total at least alpha w^2 d_w(s_w,t_w), where |M_w| <= beta*6^w and d_w(s_w,t_w) = beta*3^w).

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

theorem bcr_level_family :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℕ, 0 < β ∧ ∀ w : ℕ,
      ∃ (X : Type) (mX : MetricSpace X) (fX : Fintype X) (s t : X),
        @Fintype.card X fX ≤ (β + 1) * 6 ^ w ∧
        @dist X mX.toDist s t = (β : ℝ) * 3 ^ w ∧
        ∃ (cHi price : ℝ) (M : ℕ)
          (C : @ChunkSystemB X mX s t 0 cHi
            (α * (w : ℝ) ^ 2 * ((β : ℝ) * 3 ^ w)) price M),
          0 ≤ price ∧ (∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) := by sorry

end KServer
