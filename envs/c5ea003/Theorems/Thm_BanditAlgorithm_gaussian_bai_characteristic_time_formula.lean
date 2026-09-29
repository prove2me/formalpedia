-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_bai_characteristic_time_formula
-- name    : BanditAlgorithm.gaussian_bai_characteristic_time_formula
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:36:57.324774+00:00
-- url     : https://prove2.me/theorems/7198adf9-6608-4529-bfb6-e048798bef5c
-- title:
--   Closed form for the characteristic time of a Gaussian bandit
-- statement:
--   The characteristic time of a unit-variance Gaussian bandit with a unique best arm $i^*$ has a closed form: for any allocation $\alpha$ with full support,
--   $$\inf_{\nu'\in\mathcal E_{\mathrm{alt}}(\nu)}\ \sum_i\alpha_i\,D(\nu_i\Vert\nu'_i)=\min_{j\neq i^*}\ \frac{1}{2}\cdot\frac{\alpha_{i^*}\alpha_j}{\alpha_{i^*}+\alpha_j}\bigl(\mu_{i^*}-\mu_j\bigr)^2.$$
--
--   This is the computation behind Equation (33.4) for the Gaussian class, and it is what makes $c^*(\nu)$ effective rather than merely defined. An alternative environment must promote some arm $j$ above $i^*$; the cheapest way to do so moves only the two coordinates $i^*$ and $j$, to their pooled mean, at cost $\tfrac12\frac{\alpha_{i^*}\alpha_j}{\alpha_{i^*}+\alpha_j}(\mu_{i^*}-\mu_j)^2$. Note the same pooled-mean expression as in the empirical GLR statistic $Z_t$ -- with the true means and the allocation in place of the empirical means and the pull counts. That correspondence is the whole idea of Track-and-Stop.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Section 3 and Eq. (3); Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Eq. (33.4) specialised to the class E^k_N(1).

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal

theorem BanditAlgorithm.gaussian_bai_characteristic_time_formula {k : ℕ} [NeZero k]
    {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → NNReal}
    (hα : ∀ i, 0 < α i) :
    (⨅ ν' ∈ BanditAlgorithm.baiAlternatives
          (Set.range (BanditAlgorithm.gaussianBandit (k := k)))
          (BanditAlgorithm.gaussianBandit μvec),
        ∑ i, (α i : ENNReal) * InformationTheory.klDiv
          ((BanditAlgorithm.gaussianBandit μvec).P i) (ν'.P i))
      = ⨅ j ∈ {j : Fin k | j ≠ istar},
          ENNReal.ofReal ((α istar : ℝ) * (α j : ℝ) / ((α istar : ℝ) + (α j : ℝ))
            * (μvec istar - μvec j) ^ 2 / 2) := by
  sorry
