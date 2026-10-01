-- Prove2me | Theorems.Thm_mme_mixed_depth_regional_boundary_profile_compiler
-- name    : mme_mixed_depth_regional_boundary_profile_compiler
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-01T09:42:20.55034+00:00
-- url     : https://prove2.me/theorems/76a24b68-a823-4bb7-ab4b-eae682451b12
-- title:
--   Compile mixed-depth regional and boundary profile trees
-- statement:
--   Let $C$ be a finite certificate tree at recursive level $\ell$ on atomic CW positions $N(k)$, with source observation window $W$. Each branch consists of feasible integer regional profile packets and finite physical routing identities, or ends early with an integer boundary histogram. Spatial partitions may combine branches that terminate at different depths. The interface uses finite profiles, physical layouts, counts and coordinate grades; it does not assume extraction stages, terminal recipes, source-window inclusions or volume estimates.
--
--   Write $d(C)$ for its fixed input-degree budget, $r(C)$ for its total extraction rate, and $v(C)$ for its terminal volume rate. Boundary leaves contribute
--
--   $$L\log 2\;H_2((n_w/L)_w)+\Bigl(\sum_w n_w\,\operatorname{ones}(w)\Bigr)\log 5,$$
--
--   with value zero when $L=0$. Elementary positive leaves contribute half their total grade-one histogram count times $\log 5$. Spatial partitions add the degrees and both rates. A regional descent adds its histogram-type degree and extraction rate and retains the child volume rate. Routing coefficients are nonnegative and have a fixed finite row bound; the bound need not be one.
--
--   For every source radius $\varepsilon>0$ and volume slack $\delta>0$, there is $k_0$ such that every integer $k\ge k_0$ admits an actual graded joint recipe $E$ at level $\ell$ on $W(\varepsilon,k)$ satisfying
--
--   $$1\le U(E)\le(k+1)^{d(C)},\qquad \log O(E)=k^2r(C),$$
--   $$a(E),b(E),c(E)\ge1,\qquad \log(a(E)b(E)c(E))\ge k^2(v(C)-\delta).$$
--
--   All logarithms outside $H_2$ are natural. Empty spatial partitions and zero-length boundary leaves are included. The result assembles higher-level boundary branches with regional recursion, including the level-four AlphaEvolve application. Concrete profile values, validation of their finite routing identities, global extraction data and a strict numerical exponent surplus remain separate obligations.
-- source:
--   Auxiliary constructive compiler for the AlphaEvolve matrix-multiplication campaign. Extends the regional profile compiler and quantitative elementary volume result by allowing boundary branches to terminate at any intermediate level. Uses the existing proved scaled boundary entropy-volume estimate. Application context: https://arxiv.org/html/2608.16884v1, Sections 2.3–2.4 and 4.

import Definitions.Def_mme_mixed_depth_profile_certificate
import Theorems.Thm_mme_regional_fixed_parent_window_square_stage
import Theorems.Thm_mme_regional_supported_histograms_of_joint_certificate
import Theorems.Thm_mme_elementary_supported_stage_exact_volume
import Theorems.Thm_mme_boundary_scaled_volume_rate

open BigOperators Filter MME MME.RecursiveYZ MME.RegionRealization MME.ProfileCompiler
  MME.ProfiledCW MME.CompleteSplit MME.RecursiveYZ.CWCells MME.MixedCompiler
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000

theorem mme_mixed_depth_regional_boundary_profile_compiler
    {ell : ℕ} {N : ℕ → ℕ} {W : Window N} (C : Certificate ell N W)
    (eps delta : ℝ) (he : 0 < eps) (hd : 0 < delta) :
    ∃ k0 : ℕ, ∀ k, k0 ≤ k →
      ∃ E : LogJointRecipeG (N k) ell (W.source eps k),
        1 ≤ E.inputs ∧ E.inputs ≤ (k + 1) ^ C.degree ∧
        E.logOutputs = C.rate * k ^ 2 ∧
        1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
        (k ^ 2 : ℝ) * (C.volumeRate - delta) ≤
          Real.log ((E.a * E.b * E.c : ℕ) : ℝ) := by sorry
