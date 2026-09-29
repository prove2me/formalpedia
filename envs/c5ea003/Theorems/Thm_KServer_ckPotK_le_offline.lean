-- Prove2me | Theorems.Thm_KServer_ckPotK_le_offline
-- name    : KServer.ckPotK_le_offline
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-07T10:32:23.29401+00:00
-- url     : https://prove2.me/theorems/770ff8fb-5529-46f0-8cf1-9b5269c1aed0
-- title:
--   The Coester--Koutsoupias potential is at most $(k+1)\,\mathrm{OPT} + \Delta k(k+1)$
-- statement:
--   The Coester–Koutsoupias potential is bounded by $(k+1)$ times the offline optimum, up to an additive constant depending only on $k$ and the scale $\Delta$.
--
--   Let $M$ be a finite metric space, let $\Delta > 0$ bound all distances of $M$, let $N = M \sqcup \bar M$ be the antipodal extension of $M$ at scale $\Delta$, and let $C_0$ be a configuration of $k \ge 1$ servers in $M$. For a request sequence $\sigma$ from $M$ write $\Phi(\sigma)$ for the Coester–Koutsoupias potential (`KServer.ckPotK`), the minimum over anchors $x_1,\dots,x_k \in M$ of
--   $$\widehat w_\sigma(x_1\cdots x_k) + \sum_{i=1}^{k}\widehat w_\sigma\bigl(\bar x_i^{\,i}\,x_{i+1}\cdots x_k\bigr),$$
--   with $\widehat w_\sigma$ the unordered work function of $(C_0,\sigma)$ evaluated in $N$.
--
--   **Statement.**
--   $$\Phi(\sigma) \;\le\; (k+1)\,\mathrm{OPT}_M(C_0,\sigma) \;+\; \Delta\,k\,(k+1).$$
--
--   The potential is a sum of $k+1$ work-function values; each of them is at most the offline optimum plus the cost of one final move, and choosing the anchors to be the final configuration of an optimal offline schedule makes those final moves cost at most $2\Delta$ per relocated server. The additive term $\Delta k(k+1)$ is exactly the value the potential takes at the empty request sequence when all servers start coalesced, so this bound is what turns the potential's step inequality into a growth bound with coefficient $k+1$ and no additive slack.
--
--   **Formalization Note** $\mathrm{OPT}_M(C_0,\sigma)$ is `offlineCost C₀ σ` in the base space $M$; the potential lives on the antipodal extension, into which requests are carried by `List.map Sum.inl`.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section 'The k-server potential' (the potential is bounded by (k+1) times the offline cost up to an additive constant); E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, Section 3.4.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k

namespace KServer

theorem ckPotK_le_offline (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (σ : List M) :
    ckPotK k M Δ hΔ0 hΔ C₀ σ
      ≤ ((k : ℝ) + 1) * offlineCost C₀ σ + Δ * (k : ℝ) * ((k : ℝ) + 1) := by sorry

end KServer
