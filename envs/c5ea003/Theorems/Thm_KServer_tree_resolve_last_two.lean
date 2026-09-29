-- Prove2me | Theorems.Thm_KServer_tree_resolve_last_two
-- name    : KServer.tree_resolve_last_two
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T06:20:55.554009+00:00
-- url     : https://prove2.me/theorems/a7ef8a70-194c-426f-bebb-fab6f635b1e9
-- title:
--   CK 2021, Lemma 26 — resolving the last two anchors to the request, on trees
-- statement:
--   Let $M$ be the vertex set of a finite weighted tree, let $r$ be the last request of a $3$-server instance, and let $w$ denote the work function of that instance evaluated in the antipodal extension $M \cup \bar M$ (with $\bar p$ the antipode of $p$ at distance $2\Delta$). Then for any vertices $x, y$:
--
--   $$w(\bar x\, \bar x\, r) + w(\bar r\, \bar r\, \bar r) \;\le\; w(\bar x\, \bar x\, y) + w(\bar y\, \bar y\, \bar y) + 2\, d(r, y).$$
--
--   This is **Lemma 26 of Coester and Koutsoupias** (their `treeResolveLastTwo`) in the case $k = 3$: replacing the point $y$ by the request $r$ simultaneously in the last coordinate of the mixed configuration and in the all-antipodes configuration costs at most $(k-1) \cdot d(r,y)$ in potential terms.
--
--   ## Role
--
--   In the proof that the Work Function Algorithm is $3$-competitive on trees, the potential is a minimum of anchored sums $\Phi_{x_1x_2x_3}(w)$, and the whole argument turns on showing this minimum can be attained with the last anchor equal to the current request. The lemma is exactly the exchange step that makes the last anchor $r$: the two left-hand summands are the final two terms of $\Phi_{x\,x\,r}$-type anchored sums, the two right-hand summands the corresponding terms with anchor $y$, and the inequality says the swap to $r$ is paid for by $2\,d(r,y)$ — which the surrounding case analysis of their Theorem 23 has available.
--
--   ## Structure of the proof
--
--   The configuration $\bar x \bar x y$ **resolves** — some server moves to the request $r$ at exactly the cost of the move. If the $y$-server resolves, the first summand converts directly and the second follows from $1$-Lipschitzness, since antipodes preserve distances ($d(\bar y, \bar r) = d(y,r)$).
--
--   Otherwise an $\bar x$-server resolves, and the all-antipodes value is expanded through the McShane envelope: $w(\bar y^3) = w(a\,b\,r) + (6\Delta - a y - b y - r y)$ for some **original vertices** $a, b$ and with $r$ present — the two facts, unstated in the paper, that the envelope theorems supply. The tree now enters through its four-point condition, applied to the quadruples $(r,x,a,y)$ and $(r,x,b,y)$ of original vertices. If $r x + a y \le x y + a r$ (or the same with $b$), a chain of four $1$-Lipschitz moves through the configurations $(a, \bar y, \bar y)$ and $(a, \bar r, \bar r)$ closes the inequality. If both fail, the four-point condition forces the exact exchanges $r x + a y = r y + a x$ and $r x + b y = r y + b x$, after which two Lipschitz bounds — $\bar r^3$ against $(\bar x, y, r)$ and $\bar x \bar x r$ against $(a,b,r)$ — absorb the linear terms with equality.
--
--   ## Formalization note
--
--   The extension is `antipodalExtension` on $M \oplus M$, original vertices embedded by `Sum.inl` and antipodes written `Sum.inr`; the work function is `workFnU` of the embedded instance, so all cross-distances are literal: $d(\mathrm{inl}\,a, \mathrm{inr}\,b) = 2\Delta - d(a,b)$, $d(\mathrm{inr}\,a, \mathrm{inr}\,b) = d(a,b)$. `IsTreeVertexSpace M` supplies the four-point condition for original vertices. The proof is independent of which resolving server and which envelope minimiser are returned.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section Trees, Lemma 26 (lem:treeResolveLastTwo), case k = 3.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_tree_metric

namespace KServer

theorem tree_resolve_last_two (M : Type) [MetricSpace M] [Fintype M] (hM : IsTreeVertexSpace M)
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ : ∀ u v : M, dist u v ≤ Δ)
    (C₀ : Config 3 M) (σ : List M) (r x y : M) :
    @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr x, Sum.inr x, Sum.inl r]
      + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inr r, Sum.inr r]
    ≤ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr x, Sum.inr x, Sum.inl y]
      + @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr y, Sum.inr y, Sum.inr y]
      + 2 * dist r y := by sorry

end KServer
