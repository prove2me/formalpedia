-- Prove2me | Theorems.Thm_KServer_ckPotK_step_antipode
-- name    : KServer.ckPotK_step_antipode
-- status  : Disproved
-- author  : @Gabewhigham
-- created : 2026-09-07T10:32:26.529862+00:00
-- url     : https://prove2.me/theorems/ad73407e-ad62-4821-b139-ffd85d3c6b7d
-- title:
--   Step inequality of the Coester--Koutsoupias potential at the coalesced antipode
-- statement:
--   This is the step inequality of the Coester–Koutsoupias unifying potential: the assertion that, at every request, the potential grows at least as fast as the work function does at the coalesced antipodal configuration.
--
--   Let $M$ be a finite metric space, let $\Delta > 0$ bound all distances of $M$, and let $N = M \sqcup \bar M$ be the antipodal extension of $M$ at scale $\Delta$ (`KServer.antipodalExtension`), so that every point $q \in N$ has an antipode $\bar q$ with $d(y,q) + d(y,\bar q) = 2\Delta$ for every $y \in N$. Fix $k \ge 1$ servers with initial configuration $C_0$ drawn from $M$. For a request sequence $\tau$ from $M$, write
--   $$\widehat w_\tau(X) \;=\; \widehat w\bigl(C_0;\tau;X\bigr)$$
--   for the unordered work function of the instance evaluated in $N$, and write
--   $$\Phi(\tau) \;=\; \min_{x_1,\dots,x_k \in M}\Bigl(\widehat w_\tau(x_1\cdots x_k) + \sum_{i=1}^{k}\widehat w_\tau\bigl(\bar x_i^{\,i}\,x_{i+1}\cdots x_k\bigr)\Bigr)$$
--   for the Coester–Koutsoupias potential of that instance (`KServer.ckPotK`).
--
--   **Statement.** For every request sequence $\ell$ and every further request $r \in M$,
--   $$\widehat w_{\ell r}\bigl(\bar r^{\,k}\bigr) - \widehat w_{\ell}\bigl(\bar r^{\,k}\bigr) \;\le\; \Phi(\ell r) - \Phi(\ell),$$
--   where $\bar r^{\,k}$ is the configuration with all $k$ servers on the antipode of the request $r$.
--
--   On an antipodal space the work-function increment caused by a request is maximised, over all target configurations, at the coalesced configuration on the antipode of that request (`KServer.workFnU_growth_le_antipode`); the left-hand side is therefore the whole growth of the work function at that step. The inequality states that this growth is paid for by the potential, which is what makes $\Phi$ an amortization of the extended cost. Together with the bound $\Phi(\tau) \le (k+1)\mathrm{OPT} + \Delta k(k+1)$ and the value $\Phi(\varepsilon) = \Delta k(k+1)$ at the empty sequence for a coalesced start, it yields the sharp $(k+1)$ bound on the total work-function growth, and hence the $k$-server conjecture. This step inequality is the open part of the Coester–Koutsoupias programme; it is known for $k \le 3$, for trees and for the circle.
--
--   **Formalization Note** The work function of the extension is written with the metric-space instance `antipodalExtension M Δ hΔ0 hΔ` supplied explicitly, requests being carried into $N$ by `List.map Sum.inl` and the antipode of $r$ being `Sum.inr r`. The prefix and its one-step extension appear as `l` and `l ++ [r]`.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474 (the potential Phi and its required update/step property); E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, Section 3.4 (the extended cost lemma and the antipodal reduction).

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k

namespace KServer

theorem ckPotK_step_antipode (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (l : List M) (r : M) :
    @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
        ((l ++ [r]).map Sum.inl) (fun _ => Sum.inr r)
      - @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
        (l.map Sum.inl) (fun _ => Sum.inr r)
      ≤ ckPotK k M Δ hΔ0 hΔ C₀ (l ++ [r]) - ckPotK k M Δ hΔ0 hΔ C₀ l := by sorry

end KServer
