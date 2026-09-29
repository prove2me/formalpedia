-- Prove2me | Theorems.Thm_KServer_ckPotAtK_antipodal
-- name    : KServer.ckPotAtK_antipodal
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-07T17:14:06.954626+00:00
-- url     : https://prove2.me/theorems/7ebbc949-a285-40cc-be8f-229d178a8778
-- title:
--   On an antipodal space the potential of the doubled extension is the intrinsic potential plus $\Delta k(k+1)/2$
-- statement:
--   Let $(M,d)$ be a finite metric space that already has antipodes at scale $\Delta$: a map $a : M \to M$ with
--   $$d(x, a(y)) = \Delta - d(x,y) \qquad \text{for all } x,y \in M .$$
--   The circle of circumference $2\Delta$, and any of its finite subsets closed under the half-turn, are the standard examples.
--
--   Fix $k$ servers, an initial configuration $C_0$ and a request sequence $\sigma$ in $M$, and write $w$ for the unordered work function of that instance computed **in $M$ itself**. For an anchor tuple $x = (x_1,\dots,x_k) \in M^k$, the *intrinsic* Coester--Koutsoupias potential is
--   $$\Phi^{\mathrm{int}}_x \;=\; w(x_1 \cdots x_k) \;+\; \sum_{i=1}^{k} w\bigl(a(x_i)^{\,i}\,x_{i+1}\cdots x_k\bigr),$$
--   where $a(x_i)^{\,i}$ means $i$ servers on the antipode of $x_i$. The potential used in this mission, `KServer.ckPotAtK`, is the same expression evaluated in the *doubled* antipodal extension $N = M \sqcup \bar M$, whose added copy provides an antipode for every point of an arbitrary metric space.
--
--   **Statement.** For every anchor tuple $x$,
--   $$\Phi_x \;=\; \Phi^{\mathrm{int}}_x \;+\; \frac{\Delta\,k(k+1)}{2}.$$
--
--   That is, on a space that is antipodal to begin with, doubling the space changes the potential by an additive constant that depends only on $k$ and $\Delta$ — not on the anchor tuple, the request sequence, or the initial configuration. In particular the two potentials have exactly the same minimising anchor tuples, and the increments of the two potentials along a request sequence coincide. This is what allows the results and the counterexamples of Coester and Koutsoupias, which are stated for spaces carrying their own antipodes (the circle above all), to be read as statements about the doubled-extension potential, and conversely.
--
--   The proof is a term-by-term application of `KServer.workFnU_antipodal_extension_antipode`: the $i$-th configuration in the potential uses $i$ antipodal servers, contributing $i\Delta$, and $\sum_{i=0}^{k} i = k(k+1)/2$.
--
--   **Formalization note.** The $i$-th anchor configuration is written with a conditional, `fun j => if j ≤ i then a (x i) else x j`, matching the platform definition `KServer.ckConfigK` of the anchor configurations of the extension. Indices are $0$-based, so the summand indexed by `i : Fin k` carries `i + 1` antipodal servers.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section 3.2, equation (7) and Lemma 8 (printed pp. 7-8).

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential_k

namespace KServer

theorem ckPotAtK_antipodal (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] [Fintype M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ) (a : M → M)
    (ha : ∀ x y : M, dist x (a y) = Δ - dist x y)
    (C₀ : Config k M) (σ : List M) (x : Fin k → M) :
    ckPotAtK k M Δ hΔ0 hΔ C₀ σ x
      = (workFnU C₀ σ x
          + ∑ i : Fin k, workFnU C₀ σ (fun j => if (j : ℕ) ≤ (i : ℕ) then a (x i) else x j))
        + Δ * ((k : ℝ) * ((k : ℝ) + 1) / 2) := by sorry

end KServer
