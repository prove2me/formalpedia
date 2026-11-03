-- Prove2me | Theorems.Thm_ZeroOneIALM_property_1_ii
-- name    : ZeroOneIALM.property_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:43.890246+00:00
-- url     : https://prove2.me/theorems/557709b0-dc1e-4932-acb5-a508ec138c29
-- title:
--   Property 1 (ii): closed form of the proximal operator of $\lambda\|(\cdot)_+\|_0$
-- statement:
--   Let $\lambda,\alpha>0$. The proximal operator of $\lambda\|(\cdot)_+\|_0$ with constant $\alpha$ acts coordinatewise: for $z,u\in\mathbb R^n$,
--   $$
--   u\in\mathrm{Prox}_{\alpha\lambda\|(\cdot)_+\|_0}(z)\iff u_i\in\mathrm{Prox}_{\alpha\lambda\|(\cdot)_+\|_0}(z_i)\ \text{ for every } i,
--   $$
--   and the scalar operator is given by
--   $$
--   \mathrm{Prox}_{\alpha\lambda\|(\cdot)_+\|_0}(t)=\begin{cases}\{0\},& t\in(0,\sqrt{2\lambda\alpha}),\\ \{0,t\},& t\in\{0,\sqrt{2\lambda\alpha}\},\\ \{t\},& t\in(-\infty,0)\cup(\sqrt{2\lambda\alpha},\infty).\end{cases}
--   $$
--
--   The formula makes the primal step computable and is the source of the case analysis behind display (15).
--
--   Differences from the source:
--   - reading: [Prox(z)]ᵢ = Prox(zᵢ) for a set-valued operator → u ∈ Prox(z) if and only if uᵢ ∈ Prox(zᵢ) for every i; reason: the set of (4) is a product of scalar sets, and this is the stronger reading, which implies the equality of coordinate projections
--   - encoding: the single-valued entries 0 and zᵢ in the cases of (4) → the singleton sets {0} and {t}; reason: Prox is a set, and the printed case values denote its elements
--   - encoding: g : ℝⁿ → (−∞, ∞] → the real-valued function λ‖(·)₊‖₀ coerced to EReal in the published proximal mapping; reason: this g takes finite values only
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, Property 1 (ii), display (4), p.5

import Mathlib
import Definitions.Def_ZeroOneIALM_Prox

namespace ZeroOneIALM

/-- Property 1 (ii), Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for
Zero-One Composite Optimization, arXiv:2112.00440v1, display (4), p.5: the proximal operator of
`λ‖(·)₊‖₀` acts coordinatewise, and the scalar operator has the closed form (4).

**Formalization Note.** `[Prox(z)]ᵢ = Prox(zᵢ)` for a set-valued operator is read as: `u ∈ Prox(z)`
if and only if `uᵢ ∈ Prox(zᵢ)` for every `i`. -/
theorem property_1_ii {n : ℕ} {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α) :
    (∀ z u : EuclideanSpace ℝ (Fin n),
      u ∈ proxVec lam α z ↔ ∀ i, u i ∈ proxScalar lam α (z i)) ∧
    ∀ t : ℝ,
      (t ∈ Set.Ioo 0 (Real.sqrt (2 * lam * α)) → proxScalar lam α t = {0}) ∧
      (t ∈ ({0, Real.sqrt (2 * lam * α)} : Set ℝ) → proxScalar lam α t = {0, t}) ∧
      (t ∈ Set.Iio 0 ∪ Set.Ioi (Real.sqrt (2 * lam * α)) → proxScalar lam α t = {t}) := by sorry

end ZeroOneIALM
