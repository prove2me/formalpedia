-- Prove2me | solution 1 for mme_omega_strassen_lt
-- status  : ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-28T14:38:32.2313+00:00
-- url     : https://prove2.me/submissions/043f6fad-285e-4452-b051-6dd3bed669b8

import Mathlib.Data.Fin.VecNotation
import Theorems.Thm_mme_omega_strassen_lt
import Theorems.Thm_mme_asymptotic_sum_inequality
import Theorems.Thm_mme_schonhage_direct_sum
import Theorems.Thm_mme_omega_lt_of_sum_le

open MME BigOperators

universe u

/-! # Sketch: `matMulExp_strassen < 51/20` — Schönhage's argument

Decomposition of child B into three genuine sub-theorems:

  * `mme_asymptotic_sum_inequality` — Schönhage's τ theorem (duality);
  * `mme_schonhage_direct_sum`      — `AR(⟨4,1,4⟩ ⊕ ⟨1,9,1⟩) ≤ 17`;
  * `mme_omega_lt_of_sum_le`        — the numeric step `16^(ω/3)+9^(ω/3) ≤ 17 ⇒ ω < 51/20`.

The sketch does the real assembly: instantiate the sum inequality at the Schönhage
dimensions `n=(4,1)`, `m=(1,9)`, `p=(4,1)` with `r = 17`, discharge its hypothesis with
the direct-sum construction, evaluate the two-term sum to `16^(ω/3) + 9^(ω/3) ≤ 17`, and
close with the numeric step. -/

theorem solution {K : Type u} [Field K] :
    matMulExp_strassen K < 51 / 20 := by
  -- Sum inequality at the Schönhage dimensions, hypothesis from the direct-sum bound.
  have key : ∑ i : Fin 2,
      ((![4, 1] i * ![1, 9] i * ![4, 1] i : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤ (17 : ℕ) := by
    apply mme_asymptotic_sum_inequality (K := K) ![4, 1] ![1, 9] ![4, 1] 17
    have hb : (fun i => MMObj K (![4, 1] i) (![1, 9] i) (![4, 1] i))
            = ![MMObj K 4 1 4, MMObj K 1 9 1] := by
      funext i; fin_cases i <;> rfl
    rw [hb]; exact mme_schonhage_direct_sum
  -- Evaluate the two-term sum: 4·1·4 = 16 and 1·9·1 = 9.
  have hsum : (16 : ℝ) ^ (matMulExp_strassen K / 3) + (9 : ℝ) ^ (matMulExp_strassen K / 3) ≤ 17 := by
    rw [Fin.sum_univ_two] at key
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at key
    exact key
  -- Close with the numeric step.
  exact mme_omega_lt_of_sum_le hsum
