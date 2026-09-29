-- Prove2me | Theorems.Thm_KServer_antipodal_coalesced_growth_sum_sharp
-- name    : KServer.antipodal_coalesced_growth_sum_sharp
-- status  : Open
-- author  : @carlok
-- created : 2026-09-07T07:23:31.97133+00:00
-- url     : https://prove2.me/theorems/30cc6393-c26b-483e-8b1b-2a7cffaa3644
-- title:
--   Sharp total work-function growth at the antipodal coalesced configurations
-- statement:
--   Let $k \ge 3$, let $M$ be a finite metric space, let $\Delta > 0$ bound all distances of $M$, and let $p \in M$. Write $N = M \sqcup \bar M$ for the **antipodal extension** of $M$ at scale $\Delta$ (`KServer.antipodalExtension`): $N$ carries a copy of $M$ (via `Sum.inl`) and a second copy $\bar M$ (via `Sum.inr`), with $d(x, \bar y) = 2\Delta - d(x,y)$, so that every point $q \in N$ has an antipode $\bar q$ at distance exactly $2\Delta$ from it, and $d(y,q) + d(y,\bar q) = 2\Delta$ for **every** $y \in N$.
--
--   Start all $k$ servers of $N$ at the point $p$ (regarded in the left copy) and let $\sigma = r_0, \dots, r_{m-1}$ be a request sequence drawn from $M$, mapped into $N$ by `Sum.inl`. Write
--   $$\widehat w_t \;=\; \widehat w\bigl(p^k;\; r_0,\dots,r_{t-1};\; \cdot\bigr)$$
--   for the unordered work function of $N$ after the first $t$ requests, and let $\bar r_t \in \bar M \subseteq N$ be the antipode of the $t$-th request.
--
--   **Statement.** The total growth of the work function, *measured only at the coalesced configuration sitting on the antipode of the current request*, is at most $(k+1)$ times the offline optimum in the base space:
--   $$\sum_{t=0}^{m-1} \Bigl( \widehat w_{t+1}\bigl(\bar r_t^{\,k}\bigr) - \widehat w_{t}\bigl(\bar r_t^{\,k}\bigr) \Bigr) \;\le\; (k+1)\,\mathrm{OPT}_M\bigl(p^k, \sigma\bigr).$$
--
--   **Why this is the right formulation, and where the difficulty sits.** On an antipodal space the increment $\widehat w_{t+1}(X) - \widehat w_t(X)$ is maximised, over *all* target configurations $X$, at the coalesced configuration on the antipode of the request just served — this is `KServer.workFnU_growth_le_antipode`, already proved. Consequently the single sum above dominates the total growth $\sum_t \max_X\{\widehat w_{t+1}(X) - \widehat w_t(X)\}$, and via the isometric embedding `KServer.workFnU_antipodal_extension_restrict` it dominates the corresponding total growth in $M$ itself.
--
--   So this statement is a *concrete* form of the sharp $(k+1)$ work-function growth bound: it carries no existential over potential functions and no quantifier over target configurations. One explicit real number is attached to each step, and the assertion is a single inequality between two explicit reals. That is exactly what is needed to feed `KServer.growth_of_potential_sharp` and hence `KServer.workFnU_growth_sharp_coalesced_finite`.
--
--   The mathematical content is genuinely the open part. The coefficient $k+1$ (equivalently, $\lambda = k+1$ in the Extended Cost Lemma, giving competitive ratio $k$) is the $k$-server conjecture; Koutsoupias--Papadimitriou obtain $\lambda = 2k$ by this route (`KServer.workFnU_growth_2k_inj`), and the sharp $\lambda = k+1$ is known only for $k \le 2$ and for spaces of at most $k+2$ points (`KServer.workFnU_sharp_potential_known_cases`). Nothing here is bookkeeping: the antipodal reduction, which *is* bookkeeping, has been performed already, and what remains is the inequality itself.
--
--   **Formalization note.** `σ.getD t p` is the $t$-th request (the default `p` is irrelevant, since the sum ranges over $t < |\sigma|$). The prefixes appear as `σ.take t`, mapped into the extension by `List.map Sum.inl`. The right-hand side uses `offlineCost` in the *base* space $M$; since `Sum.inl` is an isometric embedding, the offline optimum in $N$ over `Sum.inl`-requests is at most this, so the statement as written is the weaker (and hence the correct, usable) form.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.4; E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128 (the antipodal/quasiconvexity argument and the lambda = 2k bound).

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
open KServer

theorem KServer.antipodal_coalesced_growth_sum_sharp
    (k : ℕ) (hk : 3 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (p : M) (σ : List M) :
    ∑ t ∈ Finset.range σ.length,
        (@workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun _ => Sum.inl p)
            ((σ.take (t + 1)).map Sum.inl) (fun _ => Sum.inr (σ.getD t p))
          - @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun _ => Sum.inl p)
            ((σ.take t).map Sum.inl) (fun _ => Sum.inr (σ.getD t p)))
      ≤ ((k : ℝ) + 1) * offlineCost (fun _ : Fin k => p) σ := by sorry
