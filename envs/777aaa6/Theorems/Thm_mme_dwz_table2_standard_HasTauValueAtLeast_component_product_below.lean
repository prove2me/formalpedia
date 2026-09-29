-- Prove2me | Theorems.Thm_mme_dwz_table2_standard_HasTauValueAtLeast_component_product_below
-- name    : mme_dwz_table2_standard_HasTauValueAtLeast_component_product_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T12:32:55.104397+00:00
-- url     : https://prove2.me/theorems/eee35664-a80d-4594-8b5a-0418d27dad29
-- title:
--   Strict component values assemble on the literal DWZ Table-2 standard tensor
-- statement:
--   At an integral Table-2 scale m, the DWZ standard tensor is the product of fifteen literal restricted component powers. The expected endpoint of component s is its Section 6.3 component base raised to the exact integer multiplicity c_s m. If every strict sub-endpoint is a tau-value lower bound for the corresponding restricted component power, then for arbitrary nonnegative local targets L_s below those endpoints, the complete standard tensor has tau-value at least
--
--   $$
--   \prod_{s=0}^{14} L_s.
--   $$
--
--   This gives a conditional direct component-value assembly interface beneath Equation (25) while preserving the strict endpoint convention required by asymptotic extraction arguments. It concerns the literal restricted standard object produced by the Hole Lemma, not an anonymous isomorphic tensor. The theorem does not assert its local hypotheses: the Table-2 112/121/211 estimates are coupled across cyclic factors and require a separate six-symmetrized grouped-product companion rather than fifteen independent applications.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, restricted-splitting component values and Equation (25), Section 6, especially Section 6.3 and Table 2; https://arxiv.org/abs/2210.10173

import Mathlib.Tactic
import Definitions.Def_mme_dwz_table2_standard_obj
import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_square_componentBase_pos
import Theorems.Thm_mme_finite_kronFin_HasTauValueAtLeast_product_below

open MME BigOperators
open MME.DWZSquare
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_table2_standard_HasTauValueAtLeast_component_product_below
    {K : Type u} [Field K] (m : ℕ) (tau : ℝ)
    (localTarget : Fin 15 → ℝ)
    (htarget : ∀ s, 0 ≤ localTarget s)
    (hstrict : ∀ s,
      localTarget s <
        (componentBase tau s) ^
          (MME.DWZTable2Counts.component s * m))
    (hlocal : ∀ (s : Fin 15) (W : ℝ),
      0 ≤ W →
      W <
        (componentBase tau s) ^
          (MME.DWZTable2Counts.component s * m) →
      HasTauValueAtLeast (restrictedComponentPower K s m) tau W) :
    HasTauValueAtLeast (dwzTable2StandardObj K m) tau
      (∏ s, localTarget s) := by
  sorry
