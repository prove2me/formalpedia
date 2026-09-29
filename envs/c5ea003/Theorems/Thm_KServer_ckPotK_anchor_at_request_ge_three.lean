-- Prove2me | Theorems.Thm_KServer_ckPotK_anchor_at_request_ge_three
-- name    : KServer.ckPotK_anchor_at_request_ge_three
-- status  : Disproved
-- author  : @Gabewhigham
-- created : 2026-09-07T16:48:34.060133+00:00
-- url     : https://prove2.me/theorems/3eb37b6a-da4a-4116-ac46-ccb1799dcf69
-- title:
--   The Coester--Koutsoupias potential is minimised at an anchor tuple ending in the request, for $k \ge 3$
-- statement:
--   Let $M$ be a finite metric space, let $\Delta>0$ bound all of its distances, and let $N=M\sqcup\bar M$ be the antipodal extension of $M$ at scale $\Delta$, in which the two copies carry the metric of $M$ and $d(x,\bar y)=2\Delta-d(x,y)$. Fix $k$ servers, an initial configuration $C_0$ in $M$ and a request sequence $\tau$, and write $\widehat w_\tau$ for the unordered work function of that instance evaluated in $N$. For an *anchor tuple* $x=(x_1,\dots,x_k)\in M^k$ the anchored Coester--Koutsoupias potential and the potential itself are
--
--   $$\Phi_x(\tau)=\widehat w_\tau(x_1\cdots x_k)+\sum_{i=1}^{k}\widehat w_\tau\bigl(\bar x_i^{\,i}\,x_{i+1}\cdots x_k\bigr),\qquad \Phi(\tau)=\min_{x\in M^k}\Phi_x(\tau).$$
--
--   **Statement.** For every $k\ge3$, every request sequence $\ell$ and every request $r\in M$, the minimum defining $\Phi(\ell r)$ is attained at an anchor tuple whose **last** coordinate is the request: there is $x\in M^k$ with $x_k=r$ and $\Phi_x(\ell r)=\Phi(\ell r)$.
--
--   The anchor property is what makes the step inequality of the potential exact: if $x_k=r$, every configuration of the chain of $x$ except the top one contains the request in the base copy, so its work-function value is unchanged when $r$ is appended, while the top configuration is the coalesced antipodal configuration $\bar r^{\,k}$. No Lipschitz estimate and no additive slack are needed in that deduction.
--
--   **Formalization note.** This is the case $k\ge3$ of `KServer.ckPotK_anchor_at_request`; the cases $k=1$ and $k=2$ are proved in the reduction that introduced this statement, from just two properties of the work function after the request — that it is $1$-Lipschitz for the matching distance, and that it resolves the request, in the sense that some server may be assumed to sit on it. Those two properties alone do not suffice here: there are $1$-Lipschitz functions resolving the request for which the conclusion fails once $k\ge3$, so a proof must use a further property of work functions, quasiconvexity being the natural candidate. This matches the published state of the art, where the corresponding step property is known for $k\le3$, for trees and for the circle.
--
--   **Status note (counterexample in the literature).** This statement is the hypothesis of Corollary 9 of Coester--Koutsoupias, and Section 7.2 of the same paper refutes it. On the circle of circumference $8$ with $k=3$, starting from $\{1,6,7\}$, the mixed $k$-taxi / $k$-server sequence $(6.5,6),\,4,\,(2.5,2),\,3,\,4,\,(3.5,5)$ reaches a work function $w_t$ with $\Phi(w_t)=44$, and one more request at $4$ gives $\Phi(w_{t+1})\le 45$ while $w_{t+1}(C_t)-w_t(C_t)=2$ for the WFA configuration $C_t=\{1,5,7\}$. The anchor property would force $\Phi(w_{t+1})-\Phi(w_t)\ge\max_X[w_{t+1}(X)-w_t(X)]\ge 2$. Work functions reachable by taxi requests are approximated arbitrarily well by work functions reachable by ordinary requests, so the counterexample lives on a sufficiently fine finite subset of the circle. The paper computes with the circle's intrinsic antipodes, and `KServer.ckPotAtK_antipodal` shows that on any space with intrinsic antipodes the potential of the doubled extension used here differs from the intrinsic one by the constant $\Delta k(k+1)/2$, so the two have the same minimisers and the counterexample applies to the statement as formalized. Accordingly this statement is expected to be false as stated, and a proof should not be attempted; a machine-checked disproof would require the exact work-function values on a discretized circle and is still open.
-- source:
--   Decomposition child of KServer.ckPotK_anchor_at_request; potential from C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k

namespace KServer
theorem ckPotK_anchor_at_request_ge_three (k : ℕ) (hk : 3 ≤ k) (M : Type) [MetricSpace M]
    [Fintype M] (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (l : List M) (r : M) :
    ∃ x : Fin k → M, x ⟨k - 1, by omega⟩ = r ∧
      ckPotAtK k M Δ hΔ0 hΔ C₀ (l ++ [r]) x = ckPotK k M Δ hΔ0 hΔ C₀ (l ++ [r]) := by sorry

end KServer
