-- Prove2me | Theorems.Thm_mme_CW_coupled_raw_cyclic_value_below
-- name    : mme_CW_coupled_raw_cyclic_value_below
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T14:47:49.929575+00:00
-- url     : https://prove2.me/theorems/ba61b5a4-4784-4dde-80f3-da735c55f03d
-- title:
--   Sub-base cyclic value of the coupled constituent at every q
-- statement:
--   Every base strictly below $4q^{3\tau}(q^{3\tau}+2)$ is a $\tau$-value of the cyclic symmetrisation of the coupled Coppersmith--Winograd constituent, for every $q\ge3$.
--
--   Formally: for $q\ge3$, $3\tau\ge2$ and $0\le V<4q^{3\tau}(q^{3\tau}+2)$,
--   $$\mathrm{HasTauValueAtLeast}\bigl(\mathrm{cyclicSymmetrization}(\mathrm{coupled}_q)\bigr)\,\tau\,V .$$
--
--   This is obtained from the even-power extractions of `mme_CW_coupled_tensor_extraction_below_raw` together with the admissibility of the floor profile (`mme_CW_coupled_floor_pruning`), fed into `mme_HasTauValueAtLeast_of_cofinal_finite_extractions` along the cofinal subsequence $N\mapsto 2N$ with zero error.
--
--   **Why the sub-base form.** The platform's `HasTauValueAtLeast T tau V` requires, for each fixed $\varepsilon>0$, infinitely many $N$ with an extraction achieving $V^N(1-\varepsilon)$ — a loss that does not depend on $N$. The laser construction only delivers $\mathrm{raw}^N e^{-cN^{3/4}}$, and $e^{-cN^{3/4}}$ eventually falls below any fixed $1-\varepsilon$. So the sharp base $\mathrm{raw}$ is not reachable this way, while every $V<\mathrm{raw}$ is, because $(V/\mathrm{raw})^N$ decays exponentially and therefore swallows the sub-exponential loss. This is why every value theorem along the successful $\omega<2.376$ route is stated in `_below` form.
--
--   General-$q$ form of `mme_CW_q6_coupled_raw_cyclic_value_below`.
-- source:
--   Don Coppersmith and Shmuel Winograd, Matrix multiplication via arithmetic progressions, Journal of Symbolic Computation 9(3), 1990, 251-280; the coupled four-sum constituent (d) on printed p. 266 and its value lemma on printed p. 270. General-q form of the q=6 chain used for omega < 2.376.

import Definitions.Def_mme_CW_coupled_value
open MME
universe u

theorem mme_CW_coupled_raw_cyclic_value_below
    {K : Type u} [Field K] (q : ℕ) (hq : 3 ≤ q)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (q : ℝ) ^ (3 * tau) *
        ((q : ℝ) ^ (3 * tau) + 2)) :
    HasTauValueAtLeast (cyclicSymmetrization (coupledObj K q)) tau V := by
  sorry
