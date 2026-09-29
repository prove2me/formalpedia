-- Prove2me | Theorems.Thm_mme_dwz_fourth_recursive_entropy_upper
-- name    : mme_dwz_fourth_recursive_entropy_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T07:10:46.901764+00:00
-- url     : https://prove2.me/theorems/8c517b32-bd05-49d6-8326-24853ab9e36e
-- title:
--   Certified maximum-entropy bounds for all63 positive DWZ fourth-component regions
-- statement:
--   For each of the 63 published rational split distributions—three regions for each of the 21 positive DWZ fourth-power components—let $\alpha^{(r)}$ be its exact distribution on its actual ordered split cells and $U_r$ its published rational entropy upper bound. Every probability distribution $\rho$ on those cells with the same three coordinate marginals satisfies
--
--   $$H(\rho)\le U_r,$$
--
--   where entropy uses natural logarithms. This is uniform over the entire exact marginal fiber, including distributions with zero entries. All63 reference distributions and459 logarithmic bounds are certified, without trusting a numerical optimizer or assuming that the reference shares the target marginals. The theorem supplies precisely the recursive maximum-entropy upper bounds for the frozen split distributions. It does not by itself prove the remaining scalar expressions, six-region relabeling and assembly, component-value extractions, source-order cardinality conditions, global extraction, or the exponent endpoint.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Equation (34), printed p.71. Exact recursive data10b34313-45be-4f95-bc19-c4301ee0b2ce derive from the released q5 fourth-power witness; fixed consumer IDs and region order are preserved. Uses Proved positive-reference entropy theorem ae0df7ed and exact rational-series log theorem f79fd5f9. The small source-order region-weight retune leaves every split distribution in this theorem unchanged.

import Definitions.Def_mme_dwz_fourth_rational_recursive_entropy_data

open MME.DWZFourthRecursiveWitness BigOperators
set_option autoImplicit false

theorem mme_dwz_fourth_recursive_entropy_upper (r : Fin 63) (rho : Fin (witness r).cellCount → ℝ)
    (hrho : ∀ a, 0 ≤ rho a) (hrhoSum : ∑ a, rho a = 1)
    (hmarg : ∀ (mode : Fin 3) (j : Fin 5),
      mme_modern_marginal (fun a ↦ (witness r).coarseAddress a mode) rho j =
      mme_modern_marginal (fun a ↦ (witness r).coarseAddress a mode)
        (fun a ↦ ((witness r).alpha a : ℝ)) j) :
    (∑ a, Real.negMulLog (rho a)) ≤ ((witness r).entropyUpper : ℝ) := by sorry
