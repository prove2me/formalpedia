-- Prove2me | Theorems.Thm_KServer_workFnU_antipodal_extension_antipode
-- name    : KServer.workFnU_antipodal_extension_antipode
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-07T17:10:54.11797+00:00
-- url     : https://prove2.me/theorems/5e7b417a-0283-4364-8d7f-29f1b2992cea
-- title:
--   The work function of the antipodal extension of an antipodal space
-- statement:
--   Let $(M,d)$ be a metric space that is **already antipodal at scale $\Delta$**: there is a map $a : M \to M$ with
--   $$d(x, a(y)) = \Delta - d(x,y) \qquad \text{for all } x,y \in M,$$
--   so that $a(y)$ is the antipode of $y$ and $\Delta$ is the diameter of $M$. The circle of circumference $2\Delta$ with its arc metric is the standard example, $a$ being the rotation by half the circle.
--
--   Let $N = M \sqcup \bar M$ be the antipodal extension of $M$ at scale $\Delta$ (`KServer.antipodalExtension`), in which the two copies carry the metric of $M$ and $d(x,\bar y) = 2\Delta - d(x,y)$ across the copies. Fix $k$ servers, an initial configuration $C_0$ in $M$ and a request sequence $\sigma$ in $M$, both carried into $N$ by the inclusion of the base copy, and write $\widehat w$ for the unordered work function of that instance evaluated in $N$, and $w$ for the unordered work function of the same instance evaluated in $M$.
--
--   **Statement.** For every configuration $X = (X_1,\dots,X_k)$ of $N$,
--   $$\widehat w(X) \;=\; w\bigl(\pi(X_1),\dots,\pi(X_k)\bigr) \;+\; \Delta\cdot\#\{\,i : X_i \in \bar M\,\},$$
--   where $\pi : N \to M$ is the identity on the base copy and the antipode map $a$ on the added copy $\bar M$.
--
--   The point of the identity is that on an antipodal space the added copy $\bar M$ is redundant: writing $\ell(p) \in \{0,1\}$ for the copy in which $p$ lies, the metric of $N$ splits as
--   $$d_N(p,q) \;=\; d\bigl(\pi(p),\pi(q)\bigr) \;+\; \Delta\,|\ell(p)-\ell(q)|,$$
--   because $d_N(x,\bar y) = 2\Delta - d(x,y) = \Delta + d(x,a(y))$ and $a$ is an isometry. So $N$ is two isometric copies of $M$ at "vertical" distance $\Delta$, and an offline solution pays $\Delta$ for each change of copy. Since the requests lie in the base copy, an optimal schedule stays there and moves to $\bar M$ only in the final move, paying exactly $\Delta$ for each server that ends in the added copy; conversely, along every schedule the total number of copy changes of a server that ends in $\bar M$ is at least one.
--
--   Consequently, on an antipodal space every quantity built from work-function values at configurations of the doubled extension — in particular the Coester--Koutsoupias potential $\Phi$, whose $k+1$ configurations use $0,1,\dots,k$ antipodal servers — differs from the corresponding quantity computed with the *intrinsic* antipodes of $M$ by the fixed constant $\Delta k(k+1)/2$. The identity is therefore the bridge that carries statements about the potential on antipodal spaces (the circle above all) to the doubled-extension formalization used here, and vice versa.
--
--   **Formalization note.** The count of antipodal servers is written as the sum of `Sum.elim (fun _ => 0) (fun _ => 1)` over the servers, and the projection $\pi$ as `Sum.elim id a`. The hypothesis `hΔ` (that $\Delta$ bounds all distances) is the one required to form the extension; it also follows from `ha`. The special case $X = \mathrm{inl} \circ Y$ with $Y$ a configuration of $M$ is `KServer.workFnU_antipodal_extension_restrict`, and holds without any antipodality assumption.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section 3.2 (definition of the antipodal extension and of the k-server potential, printed p. 7); E. Koutsoupias, 'Weak adversaries for the k-server problem' (1999), for the antipodal extension construction.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension

namespace KServer

theorem workFnU_antipodal_extension_antipode (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ) (a : M → M)
    (ha : ∀ x y : M, dist x (a y) = Δ - dist x y)
    (C₀ : Config k M) (σ : List M) (X : Config k (M ⊕ M)) :
    @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) (σ.map Sum.inl) X
      = workFnU C₀ σ (fun i => Sum.elim id a (X i))
        + Δ * ∑ i, Sum.elim (fun _ => (0:ℝ)) (fun _ => (1:ℝ)) (X i) := by sorry

end KServer
