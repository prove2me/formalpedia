-- Prove2me | Theorems.Thm_KServer_ckPotK_anchor_at_request_le_two
-- name    : KServer.ckPotK_anchor_at_request_le_two
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-07T17:23:45.253598+00:00
-- url     : https://prove2.me/theorems/a7ca123e-97b7-41dd-8850-ec4b2bbe88f6
-- title:
--   The Coester--Koutsoupias potential is minimised at an anchor tuple ending in the request, for $k \le 2$
-- statement:
--   Let $M$ be a finite metric space, let $\Delta>0$ bound all of its distances, and let $N = M \sqcup \bar M$ be the antipodal extension of $M$ at scale $\Delta$. Fix $k$ servers, an initial configuration $C_0$ in $M$ and a request sequence $\tau$, and write $\widehat w_\tau$ for the unordered work function of that instance evaluated in $N$. For an anchor tuple $x = (x_1,\dots,x_k) \in M^k$ the anchored Coester--Koutsoupias potential and the potential itself are
--
--   $$\Phi_x(\tau) = \widehat w_\tau(x_1\cdots x_k) + \sum_{i=1}^{k}\widehat w_\tau\bigl(\bar x_i^{\,i}\,x_{i+1}\cdots x_k\bigr), \qquad \Phi(\tau) = \min_{x \in M^k}\Phi_x(\tau).$$
--
--   **Statement.** For $k \in \{1,2\}$, every request sequence $\ell$ and every request $r \in M$, the minimum defining $\Phi(\ell r)$ is attained at an anchor tuple whose last coordinate is the request: there is $x \in M^k$ with $x_k = r$ and $\Phi_x(\ell r) = \Phi(\ell r)$.
--
--   This is the anchor condition of Corollary 9 of Coester--Koutsoupias, in the two cases where it is unconditionally true. For one server the potential after the request does not depend on the anchor at all. For two servers the argument uses only two structural properties of the work function after a request: that it is $1$-Lipschitz for the matching distance, and that it resolves the request, in the sense that
--
--   $$\widehat w_{\ell r}(a,b) = \min\bigl(\widehat h(b) + d(a,\rho),\ \widehat h(a) + d(b,\rho)\bigr), \qquad \widehat h(z) := \widehat w_{\ell r}(\rho, z),$$
--
--   where $\rho$ is the request seen in the base copy. The whole potential is thus expressible through the single $1$-Lipschitz function $\widehat h$, and the conclusion follows from a four-case comparison, each case using exactly one Lipschitz estimate.
--
--   For $k \ge 3$ these two properties no longer suffice, and the statement itself is in fact false in general: Section 7.2 of the same paper exhibits a request sequence on the circle with $k=3$ for which the potential fails the corresponding step inequality. The present statement therefore delimits the range in which the anchor condition holds unconditionally.
--
--   **Formalization note.** The last coordinate is written `x ⟨k - 1, _⟩` with $0$-based indexing. The hypothesis `hΔ` asks only that $\Delta$ be an upper bound for the distances of $M$, not that it be the diameter.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Corollary 9 (printed p. 8), the cases k = 1 and k = 2 of its hypothesis; the failure for k = 3 is Section 7.2 of the same paper (printed pp. 22-23).

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k

namespace KServer

theorem ckPotK_anchor_at_request_le_two (k : ℕ) (hk : 1 ≤ k) (hk2 : k ≤ 2) (M : Type)
    [MetricSpace M] [Fintype M] (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (l : List M) (r : M) :
    ∃ x : Fin k → M, x ⟨k - 1, by omega⟩ = r ∧
      ckPotAtK k M Δ hΔ0 hΔ C₀ (l ++ [r]) x = ckPotK k M Δ hΔ0 hΔ C₀ (l ++ [r]) := by sorry

end KServer
