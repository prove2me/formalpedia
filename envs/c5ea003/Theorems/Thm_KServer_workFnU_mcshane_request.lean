-- Prove2me | Theorems.Thm_KServer_workFnU_mcshane_request
-- name    : KServer.workFnU_mcshane_request
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T06:01:04.308485+00:00
-- url     : https://prove2.me/theorems/42f1a85f-b6c3-477a-b7ea-02748bd5920c
-- title:
--   The envelope minimizer can be taken to contain the last request
-- statement:
--   Let a $k$-server instance in $M$ (all distances $\le \Delta$) end with the request $r$, and view it in the antipodal extension $M \cup \bar M$. By the McShane envelope theorem the extension work function at any configuration $Z$ --- antipodal coordinates allowed --- is the attained minimum
--
--   $$w^{\mathrm{ext}}(Z) \;=\; \min_{X \subseteq M} \bigl( w(X) + d(X, Z) \bigr)$$
--
--   over configurations of original points. This theorem sharpens the attainment: the minimiser can moreover be taken to **contain the last request**,
--
--   $$w^{\mathrm{ext}}(Z) \;=\; w(X) + d(X, Z) \qquad \text{for some } X \subseteq M \text{ with } r \in X.$$
--
--   ## Why
--
--   Take any envelope minimiser $X$. Because $r$ is the last request, $X$ resolves: some server $x_j$ satisfies $w(X) = w(X - x_j + r) + d(x_j, r)$. Replacing $x_j$ by $r$ changes the matching cost to $Z$ in one coordinate only, and by the triangle inequality $d(r, Z_j) \le d(r, x_j) + d(x_j, Z_j)$ the increase is at most the $d(x_j, r)$ that resolution just saved. So $X - x_j + r$ is again a minimiser, and it contains $r$.
--
--   ## Role
--
--   This is the exact form in which the tree analysis of Coester and Koutsoupias consumes the envelope. Their Lemma 26 opens by writing, for the all-antipodes configuration,
--
--   $$w(\bar y^{\,k}) \;=\; w(a_1 \cdots a_{k-1}\, r) + d\bigl((a_1, \dots, a_{k-1}, r),\, \bar y^{\,k}\bigr) \quad \text{"for some } a_i \in V\text{"},$$
--
--   with the $a_i$ original tree vertices and $r$ present --- both facts unstated there, and both supplied by this theorem. Having the $a_i$ in $V$ is what lets the four-point condition of the tree metric, valid only for original points, act on them in the ensuing case analysis; having $r$ present is what the case analysis pivots on. The same expansion, at other antipodal configurations, recurs throughout their multi-ray and circle arguments.
--
--   ## Formalization note
--
--   The extension is `antipodalExtension` on $M \oplus M$ with original points embedded by `Sum.inl`; $d(X,Z)$ is the movement cost of the embedded configuration, and $w$ is `workFnU`. No finiteness of $M$ is assumed. The membership of $r$ is recorded as an index $j$ with $X_j = r$; combined with permutation invariance of the work function the minimiser can then be normalised to any desired position of $r$.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section on trees, proof of Lemma 26: the expansion w(ȳ^k) = w(a₁…a_{k−1}r) + kΔ − Σ aᵢy − ry 'for some a₁,…,a_{k−1} ∈ V', here derived rather than asserted.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension

namespace KServer

theorem workFnU_mcshane_request (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (σ : List M) (r : M) (Z : Config k (M ⊕ M)) :
    ∃ X : Config k M, (∃ j, X j = r) ∧
      @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) Z
        = workFnU C₀ (σ ++ [r]) X
          + @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (X i)) Z := by sorry

end KServer
