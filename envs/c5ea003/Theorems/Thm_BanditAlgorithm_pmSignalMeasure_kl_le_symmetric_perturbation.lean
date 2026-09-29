-- Prove2me | Theorems.Thm_BanditAlgorithm_pmSignalMeasure_kl_le_symmetric_perturbation
-- name    : BanditAlgorithm.pmSignalMeasure_kl_le_symmetric_perturbation
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T18:40:19.218349+00:00
-- url     : https://prove2.me/theorems/a5d5c665-0fdc-42f1-b512-e450dacff8d3
-- title:
--   Quadratic KL bound for perturbed partial-monitoring signals
-- statement:
--   Let $u$ be a categorical outcome distribution, let $q$ be a zero-mass perturbation direction, and suppose $u_i\ge\delta|q_i|$ for every outcome. For $0\le\Delta\le\delta/2$, let $P_c^{-}$ and $P_c^{+}$ be the feedback laws obtained by playing action $c$ under the two outcome distributions $u-\Delta q$ and $u+\Delta q$. Then
--
--   $$
--   D(P_c^{-}\Vert P_c^{+})\le \frac{8\Delta^2}{\delta}\sum_i |q_i|.
--   $$
--
--   The estimate is uniform over actions and feedback maps. It is the finite-alphabet quadratic relative-entropy estimate used in the hard partial-monitoring lower bound. Data processing passes from categorical outcome laws to feedback laws, while the coordinate margin prevents division by vanishing perturbed masses.
--
--   **Formalization Note** The outcome law and induced feedback law are the canonical objects from `PartialMonitoringStochastic`; the feedback alphabet may carry any measurable space.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (Cambridge UP, 2020), Theorem 37.12 Step 2, printed p. 490, Eq. (37.9), using the categorical KL estimate Eq. (37.4), printed p. 488, and data processing from Exercise 14.10, printed p. 196.

import Definitions.Def_PartialMonitoringStochastic
import Theorems.Thm_InformationTheory_categorical_toReal_klDiv_eq_sum
import Theorems.Thm_InformationTheory_klDiv_map_eq_klDiv_trim_comap
import Theorems.Thm_InformationTheory_klDiv_trim_le_of_isFiniteMeasure

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators

theorem BanditAlgorithm.pmSignalMeasure_kl_le_symmetric_perturbation
    {k d : ℕ} {𝕊 : Type*} [MeasurableSpace 𝕊] [NeZero d]
    (G : PartialMonitoringGame k d 𝕊) (c : Fin k)
    (u q : Fin d → ℝ) {δ Δ : ℝ}
    (hδ : 0 < δ) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ δ / 2)
    (hmargin : ∀ i, δ * |q i| ≤ u i)
    (hqsum : ∑ i, q i = 0) (humass : ∑ i, u i = 1) :
    klDiv (pmSignalMeasure G (fun i => u i - Δ * q i) c)
        (pmSignalMeasure G (fun i => u i + Δ * q i) c) ≤
      ENNReal.ofReal ((8 * Δ ^ 2 / δ) * ∑ i, |q i|) := by
  sorry
