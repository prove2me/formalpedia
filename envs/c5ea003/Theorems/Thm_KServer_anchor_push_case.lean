-- Prove2me | Theorems.Thm_KServer_anchor_push_case
-- name    : KServer.anchor_push_case
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T07:19:08.869792+00:00
-- url     : https://prove2.me/theorems/aa8f4e57-0608-4242-a2dc-22c2cf75cbea
-- title:
--   The push case of the anchoring theorem
-- statement:
--   Let $\Phi_{x_1x_2x_3}$ be the anchored Coester--Koutsoupias potential of a $3$-server instance ending with the request $r$, in the antipodal extension of a bounded space. Suppose the anchored triple $(a,b,c)$ **resolves in its first slot**: either $w(abc) = w(rbc) + d(a,r)$ (the anchor's server resolves) or $w(\bar a b c) = w(rbc) + (2\Delta - d(a,r))$ (its antipodal companion resolves). Then
--
--   $$\Phi_{bcr}(w) \le \Phi_{abc}(w) \qquad \text{or} \qquad \Phi_{cbr}(w) \le \Phi_{abc}(w).$$
--
--   ## Role
--
--   This is the terminal move of the case analysis behind Theorem 23 of Coester and Koutsoupias: whenever the current minimising triple resolves through its first anchor (or through that anchor's antipode --- the two cases are interchangeable because the first two summands of the anchored potential are symmetric in $x_1 \leftrightarrow \bar x_1$), the potential at $(r, b, c)$ is dominated, and the pushing lemma relocates $r$ from the first slot to the last, possibly transposing $b$ and $c$. Applied to a minimising triple it exhibits the potential's minimum at a triple ending with the request --- the anchoring premise from which the update property, and hence $3$-competitiveness, follows.
--
--   ## About the proof
--
--   Step one dominates $\Phi_{rbc}$ by $\Phi_{abc}$: the first summands trade places using the resolution hypothesis, and a single Lipschitz move ($\bar a \to \bar r$ at cost $d(a,r)$ in the original case, $a \to \bar r$ at cost $2\Delta - d(a,r)$ in the antipodal case) bounds the second summand; the last two summands are common. Step two is the published first-slot pushing lemma, its remainder-level disjunction upgraded to the full anchored potentials by permutation invariance of the first summand. No tree structure is used.
-- source:
--   C. Coester, E. Koutsoupias, 'Towards the k-server conjecture', ICALP 2021, arXiv:2102.10474, proof of Theorem 23, opening cases: 'If x₁x₂x₃ resolves from x₁ or x₂ … Φ(w) ≥ Φ_{rx₂x₃} by 1-Lipschitzness … lem:push3 shows Φ(w) = Φ_{yzr}(w)', including the variant through the antipodal companion x̄₁.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Definitions.Def_KServer_ck_potential

namespace KServer

theorem anchor_push_case (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) (C₀ : Config 3 M) (σ : List M) (r a b c : M)
    (h : @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl a, Sum.inl b, Sum.inl c]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl r, Sum.inl b, Sum.inl c]
          + dist a r
      ∨ @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inr a, Sum.inl b, Sum.inl c]
        = @workFnU 3 (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) ![Sum.inl r, Sum.inl b, Sum.inl c]
          + (2 * Δ - dist a r)) :
    ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) b c r ≤ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) a b c
    ∨ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) c b r ≤ ckPotAt M Δ hΔ0 hΔ C₀ (σ ++ [r]) a b c := by sorry

end KServer
