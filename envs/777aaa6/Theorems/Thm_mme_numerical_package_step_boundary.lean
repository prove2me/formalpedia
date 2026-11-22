-- Prove2me | Theorems.Thm_mme_numerical_package_step_boundary
-- name    : mme_numerical_package_step_boundary
-- status  : Disproved
-- author  : @Tamas Fulop
-- created : 2026-09-22T20:51:39.135434+00:00
-- url     : https://prove2.me/theorems/c6f1318b-26a2-4ba3-ac5e-37c0a9af2c24
-- title:
--   N equal three step-boundary package with thresholds
-- statement:
--   There is a level-three step-boundary package with room for a copy and product at least $15625$: some level, predicate, integer step, boundary over its output, and copy count with $0<\\mathit{copies}$, $\\mathit{copies}\\cdot 8^{r}\\le E_{lo}$ and $\\mathit{abc}\\ge 15625$.
--
--   This is the constructive core of the $N=3$ numerical surplus package, with the transcendental arithmetic factored out into the proved threshold lemma: three dimension-$25$ profiles give $25^3=15625$, and any step with entropy room for a copy combines with such a boundary through that lemma. It is stated without any analytic comparison, so its future proof is pure construction (profiles, grades, entropy counts).
--
--   **Formalization Note** The threshold and dimension expressions are copied verbatim from the numerical package statement so rewrites apply directly; `Predicate`, `IntegerStep` and `BoundaryEnd` resolve through the opened namespaces.
-- source:
--   N equal three step-boundary package for the numerical surplus: R. P. Stanley, Duke Math. J. 40 (1973); M. Beck et al., Amer. Math. Monthly 110 (2003) (arXiv:math/0201013). Companion to the proved N equal three surplus arithmetic; profile inventory (dim 25) after the released data.

import Definitions.Def_mme_entropy_regional_CW_recipe
import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_recursive_profiled_CW_data
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem mme_numerical_package_step_boundary : exists (lower : Nat) (P : Predicate 3) (S : IntegerStep lower 3 P) (B : BoundaryEnd lower 3 S.output) (copies : Nat), 0 < copies ∧ (((copies * 8 ^ S.repairExponent : Nat)) : Real) ≤ S.entropyLower ∧ 15625 ≤ B.a * B.b * B.c := by sorry
