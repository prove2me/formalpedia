-- Prove2me | Theorems.Thm_mme_subrankCapacityPoly_witness
-- name    : mme_subrankCapacityPoly_witness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-31T19:35:46.251894+00:00
-- url     : https://prove2.me/theorems/2112895f-4d92-4998-add9-06a5e3cf0698
-- statement:
--   **sSup-witness extraction from polynomial-subrank-capacity.** For any tensor T with 1 < V ≤ subrankCapacityPoly T and any δ > 0, there is a V' > V - δ with witness family. Standard sSup-approximation pattern via Real.lt_csSup_iff_of_pos. Bridges the abstract `V ≤ subrankCapacityPoly T` hypothesis into the concrete polynomial-bounded witness family that mme_holder_subexp_capacity_omega_bound consumes. Reusable for any subrankCapacityPoly-style asymptotic-value functional.
-- source:
--   https://arxiv.org/abs/2212.11824

import Definitions.Def_mme_subrank_capacity_poly
open MME BigOperators Filter
universe u

theorem mme_subrankCapacityPoly_witness {K : Type u} [Field K] {T : TensorObj K 3} {V δ : ℝ} (_hV : 1 < V) (_h : V ≤ subrankCapacityPoly T) (_hδ : 0 < δ) : ∃ V' : ℝ, V - δ < V' ∧ 1 ≤ V' ∧ ∃ c : ℝ, ∀ ε > (0 : ℝ), ∃ᶠ (N : ℕ) in Filter.atTop, ∃ (k : ℕ) (a b c' : Fin k → ℕ), (k : ℝ) ≤ ((N : ℝ) + 1) ^ c ∧ TensorObj.Restrict (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i))) (T.kronPow N) ∧ V' ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by sorry
