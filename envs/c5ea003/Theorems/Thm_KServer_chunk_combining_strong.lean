-- Prove2me | Theorems.Thm_KServer_chunk_combining_strong
-- name    : KServer.chunk_combining_strong
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T13:46:32.225474+00:00
-- url     : https://prove2.me/theorems/a59ab852-4a7b-4df7-b68f-4ccd3ab0a0af
-- title:
--   Chunk combining, with chunk count, trivial initial history and nonempty chunks
-- statement:
--   **The regrouping step of the recursion, with the invariants the induction needs.**
--
--   A chunk system `ChunkSystemB X s t cA cB T pe M` presents a random request sequence cut into chunks whose adapted sizes lie in the window $[c_A, c_B]$. The *combining* step of the Bubeck--Coester--Rabani induction regroups consecutive chunks so that the new chunks have (conditional) sizes close to the uniform spacing $\mathbb{E}[\Sigma]/M$: their window becomes
--
--   $$\Bigl[\ \frac{\mathbb{E}[\Sigma]}{M} - (c_B + jb),\ \ \frac{\mathbb{E}[\Sigma]}{M} + (c_B + jb)\ \Bigr],$$
--
--   where $jb$ is a Doob jump bound for the total $\Sigma$. This is what keeps the *relative* width of the size window from degrading as the recursion raises the chunk scale: grouping $b$ chunks multiplies the scale by $b$ while the window stays of width $2(c_B+jb)$, so the ratio of floor to ceiling tends to $1$ as $b$ grows.
--
--   The statement is the combining step of `KServer.chunk_combining` together with the three structural facts the next level step consumes, which that formulation does not record:
--
--   1. the regrouped system really has $M$ chunks;
--   2. its initial history is trivial;
--   3. none of its chunks is the empty list of requests, provided none of the input chunks is.
--
--   **Role.** `KServer.level_step_sturdy` requires a system with exactly $M$ chunks, trivial initial history and nonempty chunks, and returns one with the same properties; the regrouping between two level steps must therefore return them as well, or the induction cannot be iterated. Given the two-sided window in the conclusion, the remaining hypotheses of the level step (the $L^1$-sturdiness defect, the Doob jump bound needed by the *next* regrouping, the variance and the count of undersized chunks) follow from `KServer.chunk_window_invariants` and `KServer.chunk_window_variance`, so this statement is the last structural ingredient of one level of the construction.
--
--   **Formalization note.** The conclusion is an explicit existential rather than `Nonempty`, since the three extra clauses speak about the produced system. The hypotheses are exactly those of `KServer.chunk_combining`, plus nonemptiness of the input chunks, which is the form produced by the padding combinators `KServer.chunk_pad2`, `KServer.chunk_pad3` and `KServer.chunk_pad4`.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, https://arxiv.org/abs/2211.05753, Section 4, Lemma 10 (regrouping chunks onto a uniform mass grid); strengthening of the platform theorem KServer.chunk_combining with the structural invariants required by KServer.level_step_sturdy.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping

namespace KServer

theorem chunk_combining_strong {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t cA cB T pe mL)
    (h0 : ∀ ω ω' : C.Ω, C.hist 0 ω = C.hist 0 ω')
    (hch : ∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ [])
    {jbS : ℝ} (hjb : C.DoobJumpBound jbS) (hjb0 : 0 ≤ jbS) (hjbA : jbS ≤ cA)
    (hcA : 0 < cA) (hcAB : cA ≤ cB)
    {M : ℕ} (hM0 : 0 < M) {cLo' cHi' p' : ℝ}
    (hlo0 : 0 < cLo')
    (hlo : cLo' ≤ (∑ ω, C.P ω * ∑ i, C.size ω i) / M - (cB + jbS))
    (hhi : (∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS) ≤ cHi')
    (hp : pe + ((∑ ω, C.P ω * ∑ i, C.size ω i) / M + (cB + jbS)) ≤ p') :
    ∃ C' : ChunkSystemB X s t cLo' cHi' T p' M,
      C'.m = M ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      (∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) := by sorry

end KServer
