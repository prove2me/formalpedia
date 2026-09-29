-- Prove2me | Theorems.Thm_mme_integer_regional_graded_source_cofinal_extraction
-- name    : mme_integer_regional_graded_source_cofinal_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-20T19:16:03.739985+00:00
-- url     : https://prove2.me/theorems/b39ccba9-e11e-4d8e-a9ad-7c3141e3c9c6
-- title:
--   Cofinal entropy-rate extraction from an exact graded source
-- statement:
--   Consider the integer regional CW extraction construction at a scale $k$, with repair scale $k$ and total word length at most $Ck^2$. Assume fixed bounds on the half-degree, the number of fine cells, and the two finite alphabet exponents occurring in the hashing overhead. These bounds are independent of $k$.
--
--   Let $R_k$ be the summed regional entropy rate, let $L_k$ be its explicit continuity loss, and let $\Theta_k$ be the common-scale entropy exponent. Suppose
--   $$R_k-L_k\ge E k^2,\qquad \Theta_k\le Bk^2,$$
--   where $B\ge0$ and $0\le\rho<E$ are fixed. Let $Q$ be a source predicate containing every graded, exact-profile word over every target address of the integer construction.
--
--   Then there is a threshold $k_0$, depending only on the fixed bounds and rates, such that for every $k\ge k_0$ and every such integer construction, an actual repaired extraction from $Q$ exists with
--   $$\text{copies}\ge \exp(\rho k^2).$$
--   Its output predicate is exactly the graded, useful-profile predicate specified by the integer input. Over every field, the corresponding direct sum of copies is a tensor restriction of the CW tensor restricted to $Q$.
--
--   This theorem turns the explicit finite entropy guarantee into a cofinal family of actual tensor restrictions. It derives the polynomial overhead bounds from the finite size data and accounts for hashing, integer rounding, and hole repair. The graded-source hypothesis allows the source to retain an exact published parent profile; it does not require the entire typical band to satisfy that profile. Concrete component applications must still supply their integer profiles, entropy inequalities, and child tensor values.
-- source:
--   Original corollary of the platform finite entropy-copy bound (mme_integer_regional_entropy_copy_bound), subexponential repair theorem (mme_integer_regional_step_subexponential_repair), and graded-source exact-step realization (mme_recursive_region_exact_step_realization_of_graded_source, https://prove2.me/theorems/ba4853ad-7d15-4522-be6a-cdc0e3d92cc5); combines their exact formal statements without additional tensor or rate axioms. Application: the positive (1,3,4) component in the DWZ fourth-power construction.

import Theorems.Thm_mme_integer_regional_step_subexponential_repair
import Theorems.Thm_mme_integer_regional_entropy_copy_bound
import Theorems.Thm_mme_recursive_region_exact_step_realization_of_graded_source
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Mathlib

open BigOperators MME MME.RegionRate MME.RegionRealization MME.ProfiledCW
open MME.RecursiveYZ
open scoped Classical
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem mme_integer_regional_graded_source_cofinal_extraction (C H d : ℕ) (B E rho : ℝ)
    (hB : 0 ≤ B) (hrho : 0 ≤ rho) (hgap : rho < E) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ {ell M : ℕ} {P Q : Predicate M}
      (D : IntegerStep ell M P), D.repairScale = k → M ≤ C * k ^ 2 → D.half ≤ H →
      Fintype.card (Cell D.half D.R D.parent) ≤ d →
      D.R * (D.half + 1) ≤ d →
      D.R * (D.half + 1) * Fintype.card (Fin 2 → CompleteSplit.CompleteWord ell) ≤ d →
      E * (k : ℝ) ^ 2 ≤ regionalRate D.total D.n D.m D.mu -
        ((∑ r, D.n r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) D.epsilon →
      scaleExponent D.total D.n D.m D.mu D.epsilon ≤ B * (k : ℝ) ^ 2 →
      (∀ (i : Fin 3) (a : Address D.half D.R D.parent D.n),
        a ∈ RecursiveXHash.target D.m → ∀ f ∈ unbrokenWords D.total i a (D.mu i),
          Q i (ProfiledCW.flatten D.positions D.length f)) →
      ∃ S : ExactStep ell M Q,
        Real.exp (rho * (k : ℝ) ^ 2) ≤ (S.copies : ℝ) ∧ S.output = D.output ∧
        ∀ (K : Type u) [Field K], TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin S.copies ↦ tensor K D.output)) (tensor K Q) := by sorry
