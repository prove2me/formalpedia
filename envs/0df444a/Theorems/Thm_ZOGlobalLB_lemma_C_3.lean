-- Prove2me | Theorems.Thm_ZOGlobalLB_lemma_C_3
-- name    : ZOGlobalLB.lemma_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:48:52.727094+00:00
-- url     : https://prove2.me/theorems/774fd00b-b3e1-4a7c-bb31-e75ea2926ebf
-- title:
--   Lemma C.3 — mean representation and the tangent derivative of $\theta$
-- statement:
--   Let $\sigma>0$. The feature $\phi$ is a continuous map from the query strip $\mathbb R^m\times[0,1]$ into $\mathcal H$, and $\theta$ is a $C^1$ map from the unit sphere $S^{m-1}$ into $\mathcal H$. For every unit $v$ and every $(q,g)$ in the strip,
--   $$\mu_v(q,g)=4(\sqrt S-1)+\langle\theta(v),\phi(q,g)\rangle_{\mathcal H}.$$
--   For $h\perp v$ the tangent derivative satisfies
--   $$\|D\theta(v)[h]\|_{\mathcal H}^2=\frac{16m}{\sigma^2}\sum_{\ell\ge1}\ell^{-3}\|h\|^2\le\frac{20m}{\sigma^2}\|h\|^2 .$$
--
--   The hidden mean is linear in the same features as the noise, and its dependence on $v$ has a bounded derivative; together these bound the information per query.
--
--   Differences from the source:
--   - encoding: θ : S^{m−1} → H is C¹ → u ↦ θ(u/‖u‖) is C¹ on ℝᵐ ∖ {0}; Dθ(v)[h] is its derivative at v in direction h ⊥ v; reason: equivalent formulation without charts
--   - encoding: ϕ, θ as elements of H → square-summability on the strip and the sphere stated as clauses; features defined as 0 elsewhere; reason: makes the feature maps total functions
--   - reading: the derivative is continuous in sphere charts; no second derivative is required → covered by the C¹ clause; reason: remark
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma C.3, p.48, (93)

import Mathlib
import Definitions.Def_ZOGlobalLB_Field

open scoped RealInnerProductSpace

namespace ZOGlobalLB

/-- **Lemma C.3 (Mean representation and the actual tangent derivative).** Xia, Yuan,
arXiv:2610.19652, Lemma C.3, p.48, (93).

For the features in (86) and `σ > 0`: `ϕ` is continuous on the query strip and
`θ : S^{m-1} → H` is `C¹`. For every unit `v`,
`μ_v(q, g) = 4(√S - 1) + ⟨θ(v), ϕ(q, g)⟩_H` on the strip. For `h ⊥ v`, the tangent derivative
satisfies `‖Dθ(v)[h]‖²_H = (16m/σ²) Σ_{ℓ≥1} ℓ⁻³ ‖h‖² ≤ (20m/σ²)‖h‖²` (93).

**Formalization Note.**
* The feature coordinates are square-summable on the strip and on the unit sphere (first and
  third clauses), so `phiFeat`, `thetaFeat` are the genuine features (86) there.
* `C¹` on the sphere is stated without charts: `u ↦ θ(u/‖u‖)` is `C¹` on `ℝᵐ ∖ {0}`. At a unit
  `v` and `h ⊥ v`, its derivative in direction `h` is the tangent derivative `Dθ(v)[h]`.
* `Σ_{ℓ≥1} ℓ⁻³` is `∑' ℓ : ℕ, (ℓ+1)⁻³`. -/
theorem lemma_C_3 {m : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    (∀ (q : E m) (g : ℝ), g ∈ Set.Icc (0 : ℝ) 1 → Memℓp (phiSeq σ q g) 2) ∧
    ContinuousOn (fun p : E m × ℝ => phiFeat σ p.1 p.2) {p | p.2 ∈ Set.Icc (0 : ℝ) 1} ∧
    (∀ v : E m, ‖v‖ = 1 → Memℓp (thetaSeq σ v) 2) ∧
    ContDiffOn ℝ 1 (fun u : E m => thetaFeat σ (‖u‖⁻¹ • u)) {u | u ≠ 0} ∧
    (∀ v : E m, ‖v‖ = 1 → ∀ (q : E m) (g : ℝ), g ∈ Set.Icc (0 : ℝ) 1 →
      muV v q g = 4 * (Real.sqrt (Sq q g) - 1) + ⟪thetaFeat σ v, phiFeat σ q g⟫) ∧
    ∀ v : E m, ‖v‖ = 1 → ∀ h : E m, ⟪v, h⟫ = 0 →
      ‖fderiv ℝ (fun u : E m => thetaFeat σ (‖u‖⁻¹ • u)) v h‖ ^ 2 =
          16 * m / σ ^ 2 * (∑' ℓ : ℕ, ((ℓ : ℝ) + 1) ^ (-3 : ℤ)) * ‖h‖ ^ 2 ∧
      ‖fderiv ℝ (fun u : E m => thetaFeat σ (‖u‖⁻¹ • u)) v h‖ ^ 2 ≤ 20 * m / σ ^ 2 * ‖h‖ ^ 2 := by sorry

end ZOGlobalLB
