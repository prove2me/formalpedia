-- Prove2me | Theorems.Thm_KServer_chunk_system_pad
-- name    : KServer.chunk_system_pad
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-04T23:06:50.737549+00:00
-- url     : https://prove2.me/theorems/34b70a03-dfb0-4cc6-bb0e-806c6ad5deba
-- title:
--   Padding a chunk system to a metric space on exactly $k+1$ points
-- statement:
--   **Padding a chunk system to a space of exactly $k+1$ points.**
--
--   A *chunk system* `ChunkSystemB X s t cLo cHi T price M` on a metric space $X$ with marked points $s,t$ is the induction package of the Bubeck--Coester--Rabani lower bound: a finitely supported random sequence of $M$ chunks of set requests, adapted to an explicit filtration, with adapted sizes in $[c_{Lo}, c_{Hi}]$, expected total at least $T$, offline cost at most $d(s,t)$ from $s$, and the conditional guarantee that every deterministic online evader pays at least the size of a chunk on that chunk, even with an escape price available.
--
--   Constructions of such systems (for instance the recursive one of Bubeck--Coester--Rabani) produce a space whose cardinality is whatever the recursion happens to give, while statements about the $k$-server problem on $k+1$ points require the carrier to be exactly the $(k+1)$-point set. This lemma performs that adjustment.
--
--   Given a finite metric space $X$ with $|X| \le k+1$ carrying a chunk system between $s$ and $t$ with trivial initial history and total variance at most $V$, there is a metric on $\mathrm{Fin}(k+1)$ and two points $a,b$ in it with
--   $$d(a,b) \;=\; d(s,t)$$
--   carrying a chunk system between $a$ and $b$ with the *same* size window, expected total $T$, escape price and number of chunks, again with trivial initial history and total variance at most $V$.
--
--   **Role.** Combined with a construction of hard chunk systems on spaces of at most $k+1$ points, this yields hard chunk systems on exactly $k+1$ points, which is the form required by the small set chasing and $k$-server lower bounds on $(k+1)$-point metrics.
--
--   **Formalization note.** The hypotheses of trivial initial history and bounded total variance are those carried along by the platform's level-step combinators, and they are reproduced in the conclusion so that the lemma composes with them. The padded metric places the surplus points at a common distance exceeding the diameter of $X$, so that the projection sending them to a fixed point of $X$ is $1$-Lipschitz while the inclusion of $X$ is an isometry.
-- source:
--   Auxiliary lemma for S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, https://arxiv.org/abs/2211.05753, Section 4: their spaces M_w satisfy |M_w| <= beta*6^w, while the k-server statements are about metric spaces of exactly k+1 points.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

theorem chunk_system_pad {X : Type*} [MetricSpace X] [Fintype X]
    {s t : X} {cHi T price : ℝ} {M : ℕ} (k : ℕ) (hcard : Fintype.card X ≤ k + 1)
    (C : ChunkSystemB X s t 0 cHi T price M)
    (h0triv : ∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂)
    {V : ℝ}
    (hVar : ∑ ω, C.P ω * ((∑ i, C.size ω i)
      - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V) :
    ∃ (m : MetricSpace (Fin (k + 1))) (a b : Fin (k + 1)),
      @dist (Fin (k + 1)) m.toDist a b = dist s t ∧
      ∃ C' : @ChunkSystemB (Fin (k + 1)) m a b 0 cHi T price M,
        (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
        (∑ ω, C'.P ω * ((∑ i, C'.size ω i)
          - ∑ ω', C'.P ω' * (∑ i, C'.size ω' i)) ^ 2 ≤ V) := by sorry

end KServer
