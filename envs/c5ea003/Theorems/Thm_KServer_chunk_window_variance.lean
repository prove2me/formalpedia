-- Prove2me | Theorems.Thm_KServer_chunk_window_variance
-- name    : KServer.chunk_window_variance
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T13:34:42.330323+00:00
-- url     : https://prove2.me/theorems/78abc7a3-9774-418a-bdc9-159ac116bf02
-- title:
--   Variance of a chunk system from its size window
-- statement:
--   **The variance of a chunk system is controlled by its size window.**
--
--   A chunk system `ChunkSystemB X s t cLo cHi T price M` attaches to each outcome $\omega$ a sequence of $m$ chunks with sizes $c_i(\omega) \in [c_{Lo}, c_{Hi}]$. Its *total* is $\Sigma(\omega) = \sum_{i} c_i(\omega)$, and the quantity that the level step of the Bubeck--Coester--Rabani recursion carries as an invariant is the variance of that total,
--
--   $$\operatorname{Var}(\Sigma) \;=\; \sum_{\omega} P(\omega)\bigl(\Sigma(\omega) - \mathbb{E}[\Sigma]\bigr)^2 .$$
--
--   The statement bounds it by the square of the width of the interval in which the total is confined:
--
--   $$\operatorname{Var}(\Sigma) \;\le\; \bigl(m\,(c_{Hi} - c_{Lo})\bigr)^{2}.$$
--
--   Indeed the total and its mean both lie in $[m\,c_{Lo},\, m\,c_{Hi}]$, so every deviation is at most $m(c_{Hi}-c_{Lo})$ in absolute value.
--
--   **Role.** Every level step of the recursion takes a variance bound as input and returns a new one. This lemma supplies that input directly from the size window, which the regrouping combinators re-tighten at each level; it needs no probabilistic information beyond the window itself, and it is the crude bound against which sharper, construction-specific variance estimates should be compared.
-- source:
--   Auxiliary lemma for S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, https://arxiv.org/abs/2211.05753, Section 4: the variance invariant carried through the induction of Lemma 12, here bounded by the size window of the chunk system.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

theorem chunk_window_variance {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mLo) :
    ∑ ω, C.P ω * ((∑ i, C.size ω i) - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2
      ≤ ((C.m : ℝ) * (cHi - cLo)) ^ 2 := by sorry

end KServer
