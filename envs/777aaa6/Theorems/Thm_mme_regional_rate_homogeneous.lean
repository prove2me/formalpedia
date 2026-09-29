-- Prove2me | Theorems.Thm_mme_regional_rate_homogeneous
-- name    : mme_regional_rate_homogeneous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T14:36:24.681989+00:00
-- url     : https://prove2.me/theorems/8f9bbf87-fe2f-4441-93c8-ad9183ab02b1
-- title:
--   The regional extraction rate is homogeneous of degree one in the multiplicities
-- statement:
--   A regional recipe is described by integer data: region sizes $n_r$, split multiplicities $m_r(c)$ over the cells $c$, and per-mode cell word profiles $\mu_i(c, \cdot)$. Its **regional rate** is
--
--   $$\mathrm{rate} \;=\; \min\Big( \mathrm{coarse}(m, 0) - \mathrm{penalty}(n, m),\; \mathrm{parent}(\mu_1) - \mathrm{compat}(0, \mu_1),\; \mathrm{parent}(\mu_2) - \mathrm{compat}(1, \mu_2) \Big),$$
--
--   the minimum over the three modes of the retained entropy minus its compatibility cost, taken after summing over regions.
--
--   Scaling all of the data by a common positive integer $t$ — that is, replacing $n$ by $t n$, $m$ by $t m$ and $\mu$ by $t \mu$ — scales the rate by exactly $t$:
--
--   $$\mathrm{rate}(t n, t m, t \mu) \;=\; t \cdot \mathrm{rate}(n, m, \mu).$$
--
--   Each branch is built from unnormalized entropies of counts, $\mathrm{massEntropy}(x) = \sum_w -x_w\log x_w + (\sum_w x_w)\log(\sum_w x_w)$, which is homogeneous of degree one; and from quantities that depend on the data only through *normalized* distributions — the cell frequencies $\mu_c(w)/\sum_v \mu_c(v)$, the split ratios $m_r(c)/n_r$, and the parent mixture — which the scaling leaves unchanged. Since the three branches each scale by $t$ and $t \ge 0$, so does their minimum.
--
--   This is the exact statement needed to pass from a unit recipe to its $t$-fold scaling when letting $t \to \infty$: the achievable rate per unit of mass is the same at every scale, so the copy count of the scaled extraction grows like $\exp(t \cdot \mathrm{rate})$ against losses that are only polynomial in $t$.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_region_parent_profiles

open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ
open scoped Classical

universe u

set_option autoImplicit false

theorem mme_regional_rate_homogeneous {half R : ℕ} {W : Type u} [Fintype W] {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → W → ℕ) (t : ℕ) (ht : 0 < t) :
    regionalRate htotal (fun r ↦ t * n r) (fun r c ↦ t * m r c)
        (fun i c w ↦ t * mu i c w)
      = (t : ℝ) * regionalRate htotal n m mu := by sorry
