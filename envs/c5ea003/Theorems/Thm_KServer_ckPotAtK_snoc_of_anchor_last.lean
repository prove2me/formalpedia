-- Prove2me | Theorems.Thm_KServer_ckPotAtK_snoc_of_anchor_last
-- name    : KServer.ckPotAtK_snoc_of_anchor_last
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-09T16:09:58.794066+00:00
-- url     : https://prove2.me/theorems/66236743-a758-4cf4-889e-ae97437e7c43
-- title:
--   Anchored potential shift: $\Phi_x(\ell r)-\Phi_x(\ell)=\widehat w_{\ell r}(\bar r^k)-\widehat w_\ell(\bar r^k)$ for $x_k=r$
-- statement:
--   Let $M$ be a metric space, let $\Delta>0$ bound all its distances, and let $N=M\sqcup\bar M$ be the antipodal extension of $M$ at scale $\Delta$, in which every point $q$ has an antipode $\bar q$ with $d(y,q)+d(y,\bar q)=2\Delta$. Fix $k\ge 1$ servers with initial configuration $C_0$ in $M$, write $\widehat w_\tau$ for the unordered work function of the instance evaluated in $N$, and write
--   $$\Phi_x(\tau)\;=\;\widehat w_\tau(x_1\cdots x_k)\;+\;\sum_{i=1}^{k}\widehat w_\tau\bigl(\bar x_i^{\,i}\,x_{i+1}\cdots x_k\bigr)$$
--   for the anchored Coester--Koutsoupias potential of the anchor tuple $x=(x_1,\dots,x_k)$ (`KServer.ckPotAtK`).
--
--   **Statement.** For every request sequence $\ell$, every request $r\in M$ and every anchor tuple $x$ whose last coordinate is the request, $x_k=r$,
--   $$\Phi_x(\ell r)-\Phi_x(\ell)\;=\;\widehat w_{\ell r}(\bar r^{\,k})-\widehat w_{\ell}(\bar r^{\,k}).$$
--
--   In words: serving $r$ shifts the anchored potential of every anchor tuple ending at $r$ by exactly the growth of the work function at the coalesced antipode of $r$, which is the quantity appearing on the left of the Coester--Koutsoupias step inequality.
--
--   The reason is that among the $k+1$ configurations occurring in $\Phi_x$, all but the last contain the base point $r$ itself: the base configuration $x_1\cdots x_k$ has $x_k=r$, and for $i<k$ the configuration $\bar x_i^{\,i}x_{i+1}\cdots x_k$ retains the coordinate $x_k=r$. A configuration that already occupies the requested point has an unchanged work function after that request, since the work function is monotone under appending a request and the optimal schedule may stop at that configuration. The remaining configuration, the one with index $i=k$, is $\bar x_k^{\,k}=\bar r^{\,k}$, whose value grows by the stated amount.
--
--   **Formalization note.** The last coordinate is the index $\langle k-1\rangle$ of `Fin k`, whose bound follows from $1\le k$; requests are carried into $N$ by `List.map Sum.inl` and the antipode of $r$ is `Sum.inr r`.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474 (the potential Phi); the identity is the elementary observation underlying the role of the anchor property in the step inequality.

import Mathlib
import Definitions.Def_KServer_ck_potential_k

namespace KServer

theorem ckPotAtK_snoc_of_anchor_last (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ) (C₀ : Config k M)
    (l : List M) (r : M) (x : Fin k → M) (hx : x ⟨k - 1, by omega⟩ = r) :
    ckPotAtK k M Δ hΔ0 hΔ C₀ (l ++ [r]) x - ckPotAtK k M Δ hΔ0 hΔ C₀ l x
      = @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
          ((l ++ [r]).map Sum.inl) (fun _ => Sum.inr r)
        - @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (C₀ i))
          (l.map Sum.inl) (fun _ => Sum.inr r) := by sorry

end KServer
