-- Prove2me | Theorems.Thm_ZeroOneIALM_proximal_behavior
-- name    : ZeroOneIALM.proximal_behavior
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:40.615049+00:00
-- url     : https://prove2.me/theorems/9925477d-d532-4c82-87f0-4a3deb815581
-- title:
--   Proximal behavior: nonempty compact values and closed graph of $\mathrm{Prox}$
-- statement:
--   Let $\lambda,\alpha>0$. Then:
--
--   1. for every $y\in\mathbb R^n$, the set $\mathrm{Prox}_{\alpha\lambda\|(\cdot)_+\|_0}(y)$ is nonempty and compact;
--   2. if $\bar u^k\in\mathrm{Prox}_{\alpha\lambda\|(\cdot)_+\|_0}(y^k)$ for all $k$, $\bar u^k\to\bar u$ and $y^k\to y$, then $\bar u\in\mathrm{Prox}_{\alpha\lambda\|(\cdot)_+\|_0}(y)$.
--
--   These are the two consequences of Rockafellar and Wets, *Variational Analysis*, Theorem 1.25, on which the proof of Theorem 6 rests. The first makes the distance in (32b) meaningful, and the second passes the prox inclusion to the limit, giving display (80).
--
--   Differences from the source:
--   - generalization: Prox(uᵏ + αzᵏ) along the iterates, and the passage to the limit giving (80) → every y, every α > 0, and every convergent sequence with ūᵏ ∈ Prox(yᵏ); reason: the paper’s uses are instances with yᵏ = uᵏ + αzᵏ and α = 1/ρ
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, proof of Theorem 6, p.25, citing Rockafellar and Wets [33, Theorem 1.25]

import Mathlib
import Definitions.Def_ZeroOneIALM_Prox

open Filter Topology

namespace ZeroOneIALM

/-- Proximal behavior (Rockafellar and Wets, Variational Analysis, Theorem 1.25), in the two forms
used in the proof of Theorem 6, Zhang & Xiu, arXiv:2112.00440v1, p.25: `Prox_{αλ‖(·)₊‖₀}(y)` is a
nonempty compact set for every `y`, and if `ūᵏ ∈ Prox(yᵏ)`, `ūᵏ → ū` and `yᵏ → y` then
`ū ∈ Prox(y)`. -/
theorem proximal_behavior {n : ℕ} {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α) :
    (∀ y : EuclideanSpace ℝ (Fin n),
      (proxVec lam α y).Nonempty ∧ IsCompact (proxVec lam α y)) ∧
    ∀ (ubar y : ℕ → EuclideanSpace ℝ (Fin n)) (ulim ylim : EuclideanSpace ℝ (Fin n)),
      (∀ k, ubar k ∈ proxVec lam α (y k)) →
      Tendsto ubar atTop (𝓝 ulim) → Tendsto y atTop (𝓝 ylim) →
      ulim ∈ proxVec lam α ylim := by sorry

end ZeroOneIALM
