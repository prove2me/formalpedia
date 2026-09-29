-- Prove2me | Definitions.Def_KServer_workfunctionU
-- name    : KServer_workfunctionU
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-31T06:37:57.173273+00:00
-- url     : https://prove2.me/theorems/6d48e400-a2ec-43f4-8194-ac4773239996
-- title:
--   The unordered work function: the work function of an unlabelled configuration
-- statement:
--   Fix a metric space $M$, a number $k$ of servers, an initial configuration $C_0$ and a request sequence $\sigma$. In the classical treatment of the $k$-server problem a configuration is a *set* of $k$ points, and the distance between two configurations is the cost of a minimum-weight perfect matching between them; the work function $w(C_0;\sigma;X)$ is then a function of the unordered configuration $X$.
--
--   In this formalization a configuration is a labelled map $X:\{1,\dots,k\}\to M$, and `workFn` charges the final move of the offline solution for carrying server $i$ to $X(i)$. That is a stronger requirement than reaching the *set* of points of $X$, so `workFn` genuinely depends on the labelling.
--
--   **Definition.** The **unordered work function** is obtained by minimising over relabellings:
--
--   $$\widehat{w}(C_0;\sigma;X)\;=\;\min_{\pi\in\mathfrak S_k}\,w\bigl(C_0;\sigma;X\circ\pi\bigr).$$
--
--   Equivalently, it is the least cost of an offline solution that starts at $C_0$, serves $\sigma$, and finishes with its servers occupying the multiset of points of $X$ — the final move being charged as a minimum-cost matching. It therefore depends only on that multiset, and it is the classical work function.
--
--   **Why the distinction matters.** The two functions differ by at most a constant (each is within $k\cdot\mathrm{diam}$ of the other), so they define the same offline optimum: $\inf_X w=\inf_X\widehat w=\mathrm{OPT}$. But their *increments* differ, and the classical bounds on the total growth $\sum_t\max_X\{w_t(X)-w_{t-1}(X)\}$ — the quantity the Extended Cost Lemma converts into a competitive ratio — hold for $\widehat w$ and fail for $w$. On the uniform metric space of $k+1$ points with $k=2$, for instance, the labelled total growth equals $4\cdot\mathrm{OPT}$ while the unordered one equals $3\cdot\mathrm{OPT}$; the extra factor comes from configurations whose labelling is momentarily unfavourable, and it accumulates linearly in the length of the request sequence rather than being absorbed by an additive constant. Every statement in the Koutsoupias--Papadimitriou theory that quantifies over all configurations should therefore be read with $\widehat w$.
--
--   **Formalization Note** The minimum is over `Equiv.Perm (Fin k)`, a finite nonempty type, so the infimum is attained and no boundedness hypothesis is needed; `exists_eq_ciInf_of_finite` produces the minimising permutation and `ciInf_le (Finite.bddBelow_range _)` gives the bound by any particular one. The two facts that make `workFnU` usable are that a relabelling of a configuration covers the same requests, so the "serving a covered request is free" property transfers verbatim, and that `moveCost (Y ∘ π⁻¹) Z = moveCost Y (Z ∘ π)`, which lets a relabelling be moved from one argument of the movement cost to the other.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 1 (configurations as k-point sets with the minimum-weight matching distance) and Section 3.3, equation (4); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

/-- The **unordered work function**: the work function of an *unlabelled* configuration.

`workFn C₀ σ X` charges the offline solution for a final move that carries server `i` to
`X i`, so it depends on how the target configuration is labelled.  The classical work
function of Koutsoupias--Papadimitriou depends only on the *set* of points occupied, the
final move being a minimum-cost matching.  `workFnU C₀ σ X` recovers that quantity by
minimising over the relabellings of `X`; it depends only on the multiset of points of `X`,
and it is the function for which the classical properties -- quasiconvexity, duality, and
the bounds on the total growth -- are stated. -/
noncomputable def workFnU {k : ℕ} {M : Type*} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : ℝ :=
  ⨅ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π)

end KServer


