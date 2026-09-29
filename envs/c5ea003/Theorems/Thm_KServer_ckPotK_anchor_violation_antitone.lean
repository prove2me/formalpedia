-- Prove2me | Theorems.Thm_KServer_ckPotK_anchor_violation_antitone
-- name    : KServer.ckPotK_anchor_violation_antitone
-- status  : Disproved
-- author  : @Gabewhigham
-- created : 2026-09-09T16:09:34.009242+00:00
-- url     : https://prove2.me/theorems/4a165414-0377-4163-a196-5bd93915eced
-- title:
--   The anchor violation at the request is non-increasing: $V_{\ell r}(r)\le V_\ell(r)$
-- statement:
--   Let $M$ be a finite metric space, $\Delta>0$ a bound on its distances, $N=M\sqcup\bar M$ the antipodal extension at scale $\Delta$, and fix $k\ge1$ servers with initial configuration $C_0$ in $M$. For a request sequence $\tau$ write $\Phi_x(\tau)$ for the anchored Coester--Koutsoupias potential of the anchor tuple $x$ (`KServer.ckPotAtK`) and
--   $$\Phi(\tau)=\min_{x\in M^k}\Phi_x(\tau)$$
--   for the Coester--Koutsoupias potential (`KServer.ckPotK`). For a point $r\in M$ define the **anchor violation at $r$**
--   $$V_\tau(r)\;=\;\min_{x\in M^k,\; x_k=r}\Phi_x(\tau)\;-\;\Phi(\tau)\;\ge\;0,$$
--   the amount by which restricting the minimum to anchor tuples whose last coordinate is $r$ increases it. The anchor property, i.e. $V_\tau(r)=0$ whenever $r$ is the last request of $\tau$, holds for $k\le2$ but is false for $k\ge3$ (`KServer.ckPotK_anchor_at_request`, disproved on a seven-point subset of a circle).
--
--   **Statement.** For every request sequence $\ell$ and every request $r\in M$,
--   $$V_{\ell r}(r)\;\le\;V_{\ell}(r).$$
--
--   That is, serving the request $r$ does not increase the anchor violation at $r$.
--
--   This is exactly what remains of the Coester--Koutsoupias step inequality once the shift identity for anchored tuples is taken into account: because every anchor tuple with $x_k=r$ has $\Phi_x(\ell r)=\Phi_x(\ell)+G$ with $G=\widehat w_{\ell r}(\bar r^{\,k})-\widehat w_{\ell}(\bar r^{\,k})$ the growth at the coalesced antipode, the restricted minimum grows by exactly $G$, and therefore
--   $$V_{\ell r}(r)-V_{\ell}(r)\;=\;G-\bigl(\Phi(\ell r)-\Phi(\ell)\bigr).$$
--   So the displayed monotonicity is equivalent to the step inequality $G\le\Phi(\ell r)-\Phi(\ell)$, and it makes the role of the anchor property precise: the step inequality can only fail at a state where the anchor violation strictly increases, which in particular requires $V_{\ell r}(r)>0$.
--
--   **Formalization note.** The restricted minimum is written as an infimum over all tuples $x$ with the last coordinate overwritten by $r$, `Function.update x ⟨k-1, _⟩ r`; the index type is finite, so the infimum is attained.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474 (the potential Phi and its required step property).

import Mathlib
import Definitions.Def_KServer_ck_potential_k

namespace KServer

theorem ckPotK_anchor_violation_antitone (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    [Fintype M] (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (l : List M) (r : M) :
    (⨅ x : Fin k → M, ckPotAtK k M Δ hΔ0 hΔ C₀ (l ++ [r])
          (Function.update x ⟨k - 1, by omega⟩ r))
        - ckPotK k M Δ hΔ0 hΔ C₀ (l ++ [r])
      ≤ (⨅ x : Fin k → M, ckPotAtK k M Δ hΔ0 hΔ C₀ l
          (Function.update x ⟨k - 1, by omega⟩ r))
        - ckPotK k M Δ hΔ0 hΔ C₀ l := by sorry

end KServer
