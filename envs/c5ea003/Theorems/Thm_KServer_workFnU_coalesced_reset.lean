-- Prove2me | Theorems.Thm_KServer_workFnU_coalesced_reset
-- name    : KServer.workFnU_coalesced_reset
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T23:12:20.066439+00:00
-- url     : https://prove2.me/theorems/bd9b472d-4437-407c-8e3f-8f1b786c424c
-- title:
--   A finite forcing prefix realizes an injective initial work function
-- statement:
--   This lemma is **open on the platform**. It isolates a finite initialization argument and does not assert the sharp extended-cost inequality.
--
--   Fix $k\ge1$, a finite metric space $N$, an injective configuration $B$, and a point $p$. There is a finite request prefix $\rho$ whose work function from the coalesced start $p^k$ is
--   $$
--   \widehat w_{p^k,\rho}(X)=\sum_i d(p,B_i)+\widehat w_{B,\varnothing}(X)
--   $$
--   for every terminal configuration $X$. The prefix may depend on the full finite metric; the displayed offset depends only on the starting points.
--
--   A forcing-prefix argument is proposed as follows. Repeat complete cycles through all $k$ distinct points of $B$. In a finite metric, every positive move costs at least some $\delta>0$. A schedule that never occupies $B$ as a multiset must make a positive move during each full cycle: otherwise its fixed configuration covers all $k$ requested points. Choose more cycles than $(D+k\Delta)/\delta$, where $D=\sum_i d(p,B_i)$ and $\Delta$ is the diameter. A schedule can reach $B$ from $p^k$ during the first cycle at cost exactly $D$ and then match to any endpoint for at most $k\Delta$. Hence a minimizing schedule must visit $B$. Reaching $B$ costs at least $D$, and the remaining cost is at least the matching distance to the endpoint. This gives the identity. The singleton case is immediate.
--
--   The requested Lean proof must justify finite attainment, the cycle argument, and unordered matching. These steps are not supplied by the theorem declaration. Propagation of this identity through arbitrary later requests and its consequence for the offline optimum are proved separately in the finite-subspace reduction.
-- source:
--   Adaptation of the finite anchor/forcing method in Y. Emek, P. Fraigniaud, A. Korman and A. Rosen, On the Additive Constant of the k-server Work Function Algorithm (2009), Section 3, Lemma 3.3 and Corollary 3.5, https://arxiv.org/pdf/0902.1378. The exact coalesced-origin identity is the argument stated here, not a verbatim theorem from that paper. No sharp growth conjecture is used to justify the forcing argument.

import Definitions.Def_KServer_workfunctionU
open KServer

theorem KServer.workFnU_coalesced_reset (k : ℕ) (hk : 1 ≤ k)
    (M : Type) [MetricSpace M] [Fintype M] (B : Config k M)
    (hB : Function.Injective B) (p : M) :
    ∃ ρ : List M, ∀ X : Config k M,
      workFnU (fun _ => p) ρ X =
        (∑ i, dist p (B i)) + workFnU B [] X := by sorry
