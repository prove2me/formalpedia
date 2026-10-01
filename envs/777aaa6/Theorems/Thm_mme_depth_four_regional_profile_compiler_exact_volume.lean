-- Prove2me | Theorems.Thm_mme_depth_four_regional_profile_compiler_exact_volume
-- name    : mme_depth_four_regional_profile_compiler_exact_volume
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-01T08:17:36.311101+00:00
-- url     : https://prove2.me/theorems/b85af826-01ad-4536-aaa1-7a2356979258
-- title:
--   Compile depth-four regional profiles with an exact terminal volume rate
-- statement:
--   Let $L_3,L_2,L_1$ be three finite spatial layers of
--   feasible integer regional profiles on the same atomic CW positions. Each packet
--   has positive regional sizes, compatible split and mode counts, an exact joint
--   support table, admissible replicated reference addresses, and a nonnegative
--   rate strictly below its regional extraction rate. Assume finite routing
--   certificates from $L_2$ to $L_3$ and from $L_1$ to $L_2$: nonnegative coefficients
--   with row sums at most one, exact physical count identities, matching central
--   histogram identities, and grade transport.
--
--   Write $r_\ell$ for the sum of the packet rates in layer $L_\ell$, $d_\ell$ for
--   the sum of their fixed histogram-type degrees, and
--
--   $$H=\sum_{j\in L_1}\sum_{i=0}^{2}\sum_c \mu^{(j)}_{i,c,(1)}.$$
--
--   Thus $H$ is the total elementary histogram multiplicity of the one-letter
--   grade-one word, summed over packets, modes and cells. For every source radius
--   $\varepsilon>0$, there is $k_0$ such that every integer $k\ge k_0$ admits an
--   actual depth-four graded joint recipe $E$ on the source window of $L_3$ with
--
--   $$1\le U(E)\le(k+1)^{d_3+d_2},\qquad
--   \log O(E)=(r_3+r_2+r_1)k^2,$$
--   $$a(E),b(E),c(E)\ge1,\qquad
--   \log\bigl(a(E)b(E)c(E)\bigr)=k^2\frac H2\log5.$$
--
--   All logarithms are natural. The equality supplies the compiler's quantitative
--   terminal volume rate directly from finite integer profile data. No actual
--   terminal recipe, volume bound, or window inclusion is an input assumption.
--   Empty cells and empty spatial layers are allowed; regional sizes inside each
--   packet must be positive. Higher-level boundary branches are assembled separately.
--   The concrete AlphaEvolve profiles, their routing validation, global extraction
--   data and strict numerical exponent surplus are not supplied by this theorem.
-- source:
--   Auxiliary quantitative compiler theorem for the AlphaEvolve depth-four matrix-multiplication campaign, extending mme_depth_four_regional_profile_compiler (71d722ac-2d2f-4ddd-9ffc-e179332c37bf). Derived from the platform definitions and Proved fixed-window stage, joint-histogram, elementary termination, and elementary profile-dimension theorems. Application context: https://arxiv.org/html/2608.16884v1, Sections 2.3, 2.4 and 4.

import Definitions.Def_mme_regional_profile_layer_compiler_data
import Theorems.Thm_mme_regional_fixed_parent_window_square_stage
import Theorems.Thm_mme_regional_supported_histograms_of_joint_certificate
import Theorems.Thm_mme_graded_integer_step_low_level_log_recipe
import Theorems.Thm_mme_low_level_boundary_profile_dimension

open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.ProfileCompiler
  MME.ProfiledCW MME.CompleteSplit MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem mme_depth_four_regional_profile_compiler_exact_volume
    {N : ℕ → ℕ} (L3 : Layer 3 N) (L2 : Layer 2 N) (L1 : Layer 1 N)
    (H32 : Bridge L3 L2) (H21 : Bridge L2 L1)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ E : LogJointRecipeG (N k) 4 (L3.source eps k),
        1 ≤ E.inputs ∧ E.inputs ≤ (k + 1) ^ (L3.degree + L2.degree) ∧
        E.logOutputs = (L3.rate + L2.rate + L1.rate) * k ^ 2 ∧
        1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
        Real.log ((E.a * E.b * E.c : ℕ) : ℝ) =
          (k ^ 2 : ℝ) *
            (((∑ j, ∑ i : Fin 3, ∑ c, (L1.packet j).mu i c (fun _ ↦ 1) : ℕ) : ℝ) / 2 *
              Real.log 5) := by sorry
