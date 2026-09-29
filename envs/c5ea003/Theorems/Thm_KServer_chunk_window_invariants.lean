-- Prove2me | Theorems.Thm_KServer_chunk_window_invariants
-- name    : KServer.chunk_window_invariants
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-05T13:20:25.289762+00:00
-- url     : https://prove2.me/theorems/4a8336c0-ac91-4b83-a899-7a29c2c5e260
-- title:
--   Sturdiness, Doob jump bound and zero undersized-chunk count from a size window
-- statement:
--   **A narrow size window yields all three regularity invariants of the level step.**
--
--   A chunk system `ChunkSystemB X s t cLo cHi T price M` carries, for each outcome, a sequence of chunks of set requests with adapted sizes confined to the window $[c_{Lo}, c_{Hi}]$. The recursion of Bubeck--Coester--Rabani propagates three regularity invariants alongside such a system:
--
--   * **$L^1$-sturdiness** at depth $n_0$ with defect $D$: the expected positive drawdown of the Doob martingale of the total size is at most $D$ at every time $n \le n_0$, i.e.
--   $$\sum_{\omega} P(\omega)\,\bigl(\mathbb{E}[\Sigma] - \mathbb{E}[\Sigma \mid \mathcal{F}_n](\omega)\bigr)^{+} \;\le\; D, \qquad \Sigma = \textstyle\sum_i c_i;$$
--   * a **Doob jump bound** $jb$: revealing one more chunk of history moves the conditional expectation of the total mass by at most $jb$;
--   * a bound on the **expected number of undersized chunks**: chunks whose size falls below a floor $flo$, counted over the first $n \le n_0$ chunks.
--
--   The statement says that all three follow from the size window alone. Writing $m$ for the number of chunks of the system, the total size lies pointwise in $[m\,c_{Lo},\, m\,c_{Hi}]$, hence so does every conditional expectation of it; therefore both the sturdiness defect and the Doob jump are at most
--
--   $$D \;=\; jb \;=\; m\,(c_{Hi} - c_{Lo}),$$
--
--   the width of the window scaled by the number of chunks. And if the floor is at most the window's lower end, $flo \le c_{Lo}$, then no chunk among the first $n_0 \le m$ is undersized, so the expected count is $0$.
--
--   **Role.** In the recursive construction the size window is re-tightened at each regrouping, so $c_{Hi} - c_{Lo}$ is small compared with the chunk scale; this lemma converts that tightness directly into the hypotheses required by the level step `KServer.level_step_sturdy` (sturdiness and the undersized-chunk count) and by the regrouping combinator `KServer.chunk_combining` (the Doob jump bound), with no further probabilistic argument.
-- source:
--   Auxiliary lemma for S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, https://arxiv.org/abs/2211.05753, Section 4: the invariants (sturdiness, Doob jump bound, undersized-chunk count) that the induction of Lemma 12 propagates, here derived from the size window of the chunk system.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_chunk_adjust
import Definitions.Def_KServer_sturdy

namespace KServer

open ChunkSystemB

theorem chunk_window_invariants {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cLo cHi total price mLo)
    (n₀ : ℕ) (hn₀ : n₀ ≤ C.m) (flo : ℝ) (hflo : flo ≤ cLo) :
    C.SturdyL1 n₀ ((C.m : ℝ) * (cHi - cLo)) ∧
    C.DoobJumpBound ((C.m : ℝ) * (cHi - cLo)) ∧
    (∀ n ≤ n₀, ∑ ω, C.P ω *
      (∑ i ∈ Finset.range n, if C.sizeN i ω < flo then (1 : ℝ) else 0) ≤ 0) := by sorry

end KServer
