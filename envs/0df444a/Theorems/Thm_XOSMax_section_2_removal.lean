-- Prove2me | Theorems.Thm_XOSMax_section_2_removal
-- name    : XOSMax.section_2_removal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:25:12.904515+00:00
-- url     : https://prove2.me/theorems/0ac12cf7-04f5-4633-845f-e04f6c6d02c7
-- title:
--   §2 opening — removing elements with $f(v)\le0$
-- statement:
--   Let $f$ be a $k$-XOS function on a finite ground set, and let $V^+=\{v: f(v)>0\}$. The paper observes that "any v ∈ V with f(v) ≤ 0 does not contribute to increasing the function values". Precisely:
--
--   1. $f(X)\le f(X\cap V^+)$ for every $X$;
--   2. for $\alpha\ge1$, an $\alpha$-maximizer of $f$ on $V^+$ is an $\alpha$-maximizer of $f$ on the whole ground set;
--   3. if $V^+=\emptyset$ then $f(\emptyset)=0$ and $f(X)\le0$ for every $X$;
--   4. the restriction of $f$ to the subsets of $V^+$ is again $k$-XOS, with the same $k$.
--
--   This is the reduction that lets all of §2 assume $f(v)>0$.
--
--   Differences from the source:
--   - reading: a one-sentence remark that the elements can be removed → the four precise facts that the removal needs; reason: the remark has no formal statement, and these are exactly what the reduction uses
--   - encoding: the restricted instance on $V^+$ → the function on `Finset {v // 0 < f {v}}` obtained by mapping to `E`; reason: a subtype is the ground type of the restricted instance
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, §2, p.3, "any v ∈ V with f(v) ≤ 0 does not contribute to increasing the function values"

import Mathlib
import Definitions.Def_XOSMax_IsKXOS
import Definitions.Def_XOSMax_IsMaximizerApprox

namespace XOSMax

/-- The removal reduction of §2: "any v ∈ V with f(v) ≤ 0 does not contribute to increasing the
function values" (Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, §2, p.3).

With `V⁺ = { v | f(v) > 0 }`: (1) `f(X) ≤ f(X ∩ V⁺)` for every `X`; (2) an `α`-maximizer on `V⁺` is an
`α`-maximizer on the whole ground type, for `α ≥ 1`; (3) if `V⁺ = ∅` then `f(X) ≤ 0 = f(∅)` for every
`X`; (4) the restriction of `f` to the subsets of `V⁺` is again `k`-XOS, with the same width. -/
theorem section_2_removal {E : Type} [Fintype E] [DecidableEq E] {k : ℕ} (f : Finset E → ℝ)
    (hf : IsKXOS k f) :
    (∀ X : Finset E, f X ≤ f (X.filter fun v => 0 < f {v})) ∧
    (∀ (α : ℝ) (Y : Finset E), 1 ≤ α →
      IsMaximizerApprox (Finset.univ.filter fun v => 0 < f {v}) α f Y →
      IsMaximizerApprox Finset.univ α f Y) ∧
    ((Finset.univ.filter fun v => 0 < f {v}) = ∅ → f ∅ = 0 ∧ ∀ X : Finset E, f X ≤ 0) ∧
    IsKXOS k fun X : Finset {v : E // 0 < f {v}} => f (X.map (Function.Embedding.subtype _)) := by sorry

end XOSMax
