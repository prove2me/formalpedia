-- Prove2me | Theorems.Thm_mme_numerical_package_step_boundary_four
-- name    : mme_numerical_package_step_boundary_four
-- status  : Disproved
-- author  : @Tamas Fulop
-- created : 2026-09-22T21:38:27.060146+00:00
-- url     : https://prove2.me/theorems/67b9804b-fc8c-4cae-b9c3-d7de6fb7ebc6
-- title:
--   N equal four step-boundary package with thresholds
-- statement:
--   There is a level-four step-boundary package with room for a copy and product at least $390625$: some level, predicate, integer step, boundary over its output, and copy count with $0<\\mathit{copies}$, $\\mathit{copies}\\cdot 8^{r}\\le E_{lo}$ and $\\mathit{abc}\\ge 390625$.
--
--   Level four is the least feasible level: levels are even ($L\\cdot 2^{\\ell-1}=N$ with even $L$), so no level-three package exists, while four copies of a dimension-$25$ profile give $25^4=390625$. This is the constructive core of the $N=4$ numerical surplus package, with the transcendental arithmetic factored out into the proved threshold lemma.
--
--   **Formalization Note** The threshold and dimension expressions match the numerical package statement verbatim so rewrites apply directly.
-- source:
--   N equal four step-boundary package for the numerical surplus (least feasible level): R. P. Stanley, Duke Math. J. 40 (1973); M. Beck et al., Amer. Math. Monthly 110 (2003) (arXiv:math/0201013). Companion to the proved N equal four surplus arithmetic.

import Definitions.Def_mme_entropy_regional_CW_recipe
import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_recursive_profiled_CW_data
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_numerical_package_step_boundary_four : exists (lower : Nat) (P : Predicate 4) (S : IntegerStep lower 4 P) (B : BoundaryEnd lower 4 S.output) (copies : Nat), 0 < copies ∧ (((copies * 8 ^ S.repairExponent : Nat)) : Real) ≤ S.entropyLower ∧ 390625 ≤ B.a * B.b * B.c := by sorry
