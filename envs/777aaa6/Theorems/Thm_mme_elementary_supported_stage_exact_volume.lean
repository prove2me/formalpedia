-- Prove2me | Theorems.Thm_mme_elementary_supported_stage_exact_volume
-- name    : mme_elementary_supported_stage_exact_volume
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-01T08:12:24.187366+00:00
-- url     : https://prove2.me/theorems/a5fc84ac-0340-4002-8e0e-ab1ea5a69acd
-- title:
--   Exact terminal matrix volume of a supported elementary regional type
-- statement:
--   Let $D$ be a graded regional part stage at elementary depth, with source predicate $S$, target predicate $T$, and certified logarithmic output rate $\rho(D)$. Let $u>1$ be a terminal recipe level, and let $x=(x_0,x_1,x_2)$ be a supported target triple on $M$ atomic CW positions. Thus each $x_i$ lies in $T_i$, and the three grades at every position sum to two. Define
--
--   $$H(x)=\sum_{i=0}^{2}\sum_{r=1}^{M}\mathbf{1}_{\{x_i(r)=1\}}.$$
--
--   There exists an actual terminal graded joint recipe $E$ at level $u$ for $S$, with
--
--   $$U(E)=1,\qquad \log O(E)=\rho(D),\qquad a(E),b(E),c(E)\ge1,$$
--   $$\bigl(a(E)b(E)c(E)\bigr)^2=5^{H(x)}.$$
--
--   This identifies the elementary matrix volume of the feasible exact type covering the specified supported triple. It gives quantitative volume information without a separate dimension-growth assumption. Empty cells and empty position families are allowed. It does not supply the AlphaEvolve numerical witness or establish the final exponent margin.
-- source:
--   Auxiliary theorem for the AlphaEvolve depth-four matrix-multiplication campaign. Dependencies: mme_graded_integer_step_low_level_log_recipe (fb00c9d5-f808-4c12-a2b7-bcfbc5088e5d) and mme_low_level_boundary_profile_dimension (d210d623-684d-4521-b138-466575bc5406). Derived directly from the platform definitions; application context: https://arxiv.org/html/2608.16884v1, Section 2.3.

import Theorems.Thm_mme_graded_integer_step_low_level_log_recipe
import Theorems.Thm_mme_low_level_boundary_profile_dimension

open BigOperators MME MME.RecursiveYZ MME.ProfiledCW MME.CompleteSplit
  MME.RegionRealization MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem mme_elementary_supported_stage_exact_volume
    {M upper : ℕ} {S T : Predicate M}
    (D : LogPartStageG M 1 S T) (hupper : 1 < upper)
    (x : Fin 3 → FineWord M) (hs : supported x) (ht : ∀ i, T i (x i)) :
    ∃ E : LogJointRecipeG M upper S,
      E.inputs = 1 ∧ E.logOutputs = D.rate ∧
      1 ≤ E.a ∧ 1 ≤ E.b ∧ 1 ≤ E.c ∧
      (E.a * E.b * E.c) ^ 2 =
        5 ^ (∑ i : Fin 3, ∑ r : Fin M, if x i r = 1 then 1 else 0) := by sorry
