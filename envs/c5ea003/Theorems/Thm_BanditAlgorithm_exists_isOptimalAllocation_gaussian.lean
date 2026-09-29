-- Prove2me | Theorems.Thm_BanditAlgorithm_exists_isOptimalAllocation_gaussian
-- name    : BanditAlgorithm.exists_isOptimalAllocation_gaussian
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:50:48.22051+00:00
-- url     : https://prove2.me/theorems/589f5f6d-b712-4d84-97c3-e4425fa37d39
-- title:
--   An optimal allocation exists and has full support
-- statement:
--   Every unit-variance Gaussian bandit with a unique best arm admits an optimal allocation with full support: there exists $\alpha\in\mathcal P_{k-1}$ with $\alpha_i>0$ for all $i$ attaining the supremum in
--   $$c^*(\nu)^{-1}=\sup_{\alpha\in\mathcal P_{k-1}}\ \inf_{\nu'\in\mathcal E_{\mathrm{alt}}(\nu)}\ \sum_i\alpha_i D(\nu_i\Vert\nu'_i).$$
--
--   This is the object Track-and-Stop tracks -- line 8 of Algorithm 21 plugs the empirical means into $\alpha^*(\cdot)$ and drives the empirical allocation $T_i(t)/t$ towards the result -- so both the existence and the strict positivity matter: full support is what lets the plug-in estimate be consistent. Existence is compactness of the simplex against upper semicontinuity of the objective; full support holds because the objective vanishes whenever some coordinate does, so no boundary point can be optimal.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Section 3 (existence and uniqueness of the optimal weights); Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Eq. (33.4) and Algorithm 21.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.exists_isOptimalAllocation_gaussian {k : ℕ} [NeZero k]
    {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    ∃ α : Fin k → NNReal, (∀ i, 0 < α i) ∧
      BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
        (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α := by
  sorry
