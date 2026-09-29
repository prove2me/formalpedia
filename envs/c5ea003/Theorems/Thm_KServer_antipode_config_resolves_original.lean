-- Prove2me | Theorems.Thm_KServer_antipode_config_resolves_original
-- name    : KServer.antipode_config_resolves_original
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T06:38:14.189602+00:00
-- url     : https://prove2.me/theorems/b016fcb5-238b-4e9e-9adf-d742db72f026
-- title:
--   A configuration holding the request's antipode resolves through an original server
-- statement:
--   Let $w$ be the work function of a $3$-server instance ending with the request $r$, in the antipodal extension of a bounded space, and consider a configuration $(\bar r, y, z)$ holding the request's antipode together with two original points. Every configuration resolves --- some server moves to $r$ at exactly the cost of the move --- but a priori the resolving server could be the one at $\bar r$, whose move costs the full $2\Delta$. The theorem rules that out as the only option:
--
--   $$w(\bar r, y, z) = w(\bar r, r, z) + d(y,r) \qquad \text{or} \qquad w(\bar r, y, z) = w(\bar r, y, r) + d(z,r):$$
--
--   **the configuration always resolves through one of its original servers**, never only through the antipode.
--
--   ## Why
--
--   The one-sided bounds $w(\bar r, y, z) \le w(\bar r, r, z) + d(y,r)$ (and with $z$) are $1$-Lipschitzness; the content is that one of them is tight. By the envelope theorem the value $w(\bar r, y, z)$ is attained through an original configuration $A \ni r$, matched coordinatewise: the $\bar r$-slot contributes $2\Delta - d(A_0, r)$ and the $y$- and $z$-slots contribute plainly. If $r$ sits in $A$ facing the $y$-slot, replacing $y$ by $r$ in the target *removes* exactly $d(y,r)$ from the matching, so the $y$-resolution is tight; likewise for $z$. The interesting case is $r$ facing the $\bar r$-slot: then one *permutes* $A$ --- the work function is blind to the relabelling, the matching is not --- so that $r$ faces $\bar r$'s neighbour instead, and the triangle inequality $d(y,r) \le d(A_1, y) + d(A_1, r)$ shows the permuted matching still pays for the $y$-resolution. So an original-server resolution is always available.
--
--   ## Role
--
--   This is the missing case in the proof of Lemma 21 of Coester and Koutsoupias (the lemma that pushes the request to the last anchor slot, valid for $k \le 3$ and false for $k = 4$). Their argument resolves the configuration $\bar r^{\,k-2} y z$ and treats the resolutions from $y$ and from $z$, tacitly discarding resolution from $\bar r$; this theorem is the justification: a $y$- or $z$-resolution always exists, whatever the resolution oracle returns. It feeds directly into the first-slot pushing lemma and thence into the case analysis of their Theorem 23 on trees.
--
--   ## Formalization note
--
--   Stated in the antipodal extension on $M \oplus M$ with originals embedded by `Sum.inl` and $\bar r = \mathrm{Sum.inr}\, r$; $w$ is `workFnU`. The proof uses only the envelope theorems and permutation invariance --- no tree structure, no finiteness of $M$.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, proof of Lemma 21 (lem:push3): the resolution case analysis of w(r̄^{k-2} y z), whose resolution-from-r̄ branch is tacitly discarded there; this theorem justifies the omission for k = 3.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension

namespace KServer

theorem antipode_config_resolves_original (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) (C₀ : Config 3 M) (σ : List M) (r y z : M) :
    @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inl y, Sum.inl z]
      = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inl r, Sum.inl z]
        + dist y r
    ∨ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
        (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inl y, Sum.inl z]
      = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr r, Sum.inl y, Sum.inl r]
        + dist z r := by sorry

end KServer
