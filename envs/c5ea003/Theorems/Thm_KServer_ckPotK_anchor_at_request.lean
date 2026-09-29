-- Prove2me | Theorems.Thm_KServer_ckPotK_anchor_at_request
-- name    : KServer.ckPotK_anchor_at_request
-- status  : Disproved
-- author  : @Gabewhigham
-- created : 2026-09-07T13:18:06.663484+00:00
-- url     : https://prove2.me/theorems/0b375c0c-91c9-477d-8581-79e3bc779f19
-- title:
--   The Coester–Koutsoupias potential is minimised at an anchor tuple ending in the request
-- statement:
--   Let $M$ be a finite metric space, let $\Delta>0$ bound all its distances, and let $N = M\sqcup\bar M$ be the antipodal extension of $M$ at scale $\Delta$. For $k\ge 1$ servers with initial configuration $C_0$ in $M$ and a request sequence $\tau$, write $\widehat w_\tau$ for the unordered work function of the instance evaluated in $N$, and, for an *anchor tuple* $x=(x_1,\dots,x_k)\in M^k$,
--   $$\Phi_x(\tau) \;=\; \widehat w_\tau(x_1\cdots x_k) \;+\; \sum_{i=1}^{k}\widehat w_\tau\bigl(\bar x_i^{\,i}\,x_{i+1}\cdots x_k\bigr),\qquad \Phi(\tau)=\min_{x\in M^k}\Phi_x(\tau)$$
--   for the anchored Coester–Koutsoupias potential and the potential itself.
--
--   **Statement.** For every request sequence $\ell$ and every request $r\in M$, the minimum defining $\Phi(\ell r)$ is attained at an anchor tuple whose **last** coordinate is the request: there is $x\in M^k$ with $x_k=r$ and $\Phi_x(\ell r)=\Phi(\ell r)$.
--
--   **Why this is the right statement.** It implies the step inequality of the potential with no loss whatsoever. Indeed, if $x_k=r$ then every configuration of the chain $\Phi_x$ except the top one contains the request $r$ in the base copy of $M$, so its work-function value is unchanged when the request $r$ is appended; and the top configuration of the chain is exactly $\bar r^{\,k}$, the coalesced configuration on the antipode of the request. Hence
--   $$\Phi_x(\ell r)-\Phi_x(\ell) \;=\; \widehat w_{\ell r}(\bar r^{\,k})-\widehat w_{\ell}(\bar r^{\,k}),$$
--   and combining this with $\Phi(\ell)\le\Phi_x(\ell)$ gives the step inequality. No Lipschitz estimate, no triangle inequality and no additive slack are used in that deduction.
--
--   **What is known.** The statement is proved for $k=1$ (where the potential does not depend on the anchor at all) and for $k=2$, in both cases from just two properties of the work function after the request: that it is $1$-Lipschitz for the matching distance, and that it is *tight* at the request (some server may be assumed to sit on $r$). Those two properties alone do **not** suffice for $k\ge 3$: there are $1$-Lipschitz functions, tight at the request, for which the conclusion fails. A proof for $k\ge 3$ must therefore use a further property of work functions, quasiconvexity being the natural candidate; this matches the published proofs, which reach $k\le 3$, trees and the circle.
--
--   **Status note (counterexample in the literature).** This statement is the hypothesis of Corollary 9 of Coester--Koutsoupias, and Section 7.2 of the same paper refutes it. On the circle of circumference $8$ with $k=3$, starting from $\{1,6,7\}$, the mixed $k$-taxi / $k$-server sequence $(6.5,6),\,4,\,(2.5,2),\,3,\,4,\,(3.5,5)$ reaches a work function $w_t$ with $\Phi(w_t)=44$, and one more request at $4$ gives $\Phi(w_{t+1})\le 45$ while $w_{t+1}(C_t)-w_t(C_t)=2$ for the WFA configuration $C_t=\{1,5,7\}$. The anchor property would force $\Phi(w_{t+1})-\Phi(w_t)\ge\max_X[w_{t+1}(X)-w_t(X)]\ge 2$. Work functions reachable by taxi requests are approximated arbitrarily well by work functions reachable by ordinary requests, so the counterexample lives on a sufficiently fine finite subset of the circle. The paper computes with the circle's intrinsic antipodes, and `KServer.ckPotAtK_antipodal` shows that on any space with intrinsic antipodes the potential of the doubled extension used here differs from the intrinsic one by the constant $\Delta k(k+1)/2$, so the two have the same minimisers and the counterexample applies to the statement as formalized. Accordingly this statement is expected to be false as stated, and a proof should not be attempted; a machine-checked disproof would require the exact work-function values on a discretized circle and is still open.
-- source:
--   Decomposition child of KServer.ckPotK_step_antipode; potential from C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k

namespace KServer
theorem ckPotK_anchor_at_request (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (l : List M) (r : M) :
    ∃ x : Fin k → M, x ⟨k - 1, by omega⟩ = r ∧
      ckPotAtK k M Δ hΔ0 hΔ C₀ (l ++ [r]) x = ckPotK k M Δ hΔ0 hΔ C₀ (l ++ [r]) := by sorry

end KServer
