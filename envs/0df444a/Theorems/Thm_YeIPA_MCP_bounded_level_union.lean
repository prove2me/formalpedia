-- Prove2me | Theorems.Thm_YeIPA_MCP_bounded_level_union
-- name    : YeIPA.MCP.bounded_level_union
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:58:36.647921+00:00
-- url     : https://prove2.me/theorems/4edaa80d-7b61-4021-aef6-fe9568782cd3
-- title:
--   Lemma 8.21 — the union of the level sets $C_{++}(\theta r,\delta)$, $\theta\in[\theta^0,\theta^1]$, is bounded
-- statement:
--   Let $f$ be a continuous monotone map from $\mathbb R^n_{++}$ to $\mathbb R^n$, with $S_{++}(r)=\{(x,s)\in\mathbb R^{2n}_{++}: s=f(x)+r\}$ and, for $\delta>0$, $C_{++}(r,\delta)=\{(x,y)\in S_{++}(r): x^Ty\le\delta\}$. Let $r\in\mathbb R^n$ and $\theta^0\le\theta^1$, and assume $S_{++}(\theta^0r)\ne\emptyset$ and $S_{++}(\theta^1r)\ne\emptyset$. Then for every $\delta>0$ the set
--   $$\bigcup_{\theta\in[\theta^0,\theta^1]}C_{++}(\theta r,\delta)\subseteq\mathbb R^n\times\mathbb R^n$$
--   is bounded.
--
--   This compactness statement is what allows limits along the segment $\theta\in[\theta^0,\theta^1]$ in the proof that $R_{++}$ is convex.
--
--   **Formalization Note** The standing assumptions of §8.4.1 (continuity and monotonicity of $f$ on $\mathbb R^n_{++}$) are explicit hypotheses. Boundedness is `Bornology.IsBounded` in the product of the two coordinate spaces (any norm gives the same notion).
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 258, Lemma 8.21

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix

namespace YeIPA.MCP

/-- Lemma 8.21 (Ye 1997, p. 258). Let `f` be continuous and monotone on `ℝⁿ₊₊` (standing
assumption of §8.4.1, p. 257), `r ∈ ℝⁿ` and `θ⁰ ≤ θ¹`, and assume `S₊₊(θ⁰r) ≠ ∅` and
`S₊₊(θ¹r) ≠ ∅`. Then for every `δ > 0` the union over `θ ∈ [θ⁰, θ¹]` of
`C₊₊(θr, δ) = {(x, y) ∈ S₊₊(θr) : xᵀy ≤ δ}` is bounded. -/
theorem bounded_level_union {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f)
    (r : Fin n → ℝ) (θ₀ θ₁ : ℝ) (hθ : θ₀ ≤ θ₁)
    (h₀ : (Spp f (θ₀ • r)).Nonempty) (h₁ : (Spp f (θ₁ • r)).Nonempty) :
    ∀ δ : ℝ, 0 < δ → Bornology.IsBounded (⋃ θ ∈ Set.Icc θ₀ θ₁, Cpp f (θ • r) δ) := by sorry

end YeIPA.MCP
