-- Prove2me | solution 1 for bernoulli_moment_from_two_sided_mgf
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-22T02:26:25.413225+00:00
-- url     : https://prove2.me/submissions/e5763eb9-dbeb-48ab-a905-bec89e7991c7

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_rpow_mul_exp_neg_le
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1000000

/-- **Moment-from-MGF on the Bernoulli powerset measure.** If a real statistic `Z`
has both-sided MGF bounded by `M` at parameter `lam > 0`
(`E[e^{lam·Z}] ≤ M` and `E[e^{-lam·Z}] ≤ M`), then for every real `q > 0`,
`E[|Z|^q] ≤ 2·(q/(lam·e))^q·M`. (Cramér–Chernoff moment device.) -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (lam M q : ℝ)
    (hlam : 0 < lam) (hq : 0 < q)
    (hMGFpos : bernoulliExpectation p (fun Omega => Real.exp (lam * Z Omega)) ≤ M)
    (hMGFneg : bernoulliExpectation p (fun Omega => Real.exp (-(lam * Z Omega))) ≤ M) :
    bernoulliExpectation p (fun Omega => |Z Omega| ^ q) ≤
      2 * (q / (lam * Real.exp 1)) ^ q * M := by
  classical
  -- pointwise: |Z Ω|^q ≤ (q/(lam e))^q (e^{lam Z}+e^{-lam Z}).
  have hpoint : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      |Z Omega| ^ q ≤ (q / (lam * Real.exp 1)) ^ q *
        (Real.exp (lam * Z Omega) + Real.exp (-(lam * Z Omega))) := by
    intro Om
    -- |Z|^q * e^{-lam|Z|} ≤ (q/(lam e))^q  ⇒ |Z|^q ≤ (q/(lam e))^q e^{lam|Z|}
    have hx : (0:ℝ) ≤ |Z Om| := abs_nonneg _
    have hbase := rpow_mul_exp_neg_le q lam (|Z Om|) hq hlam hx
    have hepos : (0:ℝ) < Real.exp (-(lam * |Z Om|)) := Real.exp_pos _
    -- |Z|^q ≤ (q/(lam e))^q * e^{lam|Z|}
    have hstep : |Z Om| ^ q ≤ (q / (lam * Real.exp 1)) ^ q * Real.exp (lam * |Z Om|) := by
      have hle : |Z Om| ^ q ≤ (q / (lam * Real.exp 1)) ^ q / Real.exp (-(lam * |Z Om|)) :=
        (le_div_iff₀ hepos).mpr hbase
      calc |Z Om| ^ q ≤ (q / (lam * Real.exp 1)) ^ q / Real.exp (-(lam * |Z Om|)) := hle
        _ = (q / (lam * Real.exp 1)) ^ q * Real.exp (lam * |Z Om|) := by
            rw [Real.exp_neg, div_inv_eq_mul]
    -- e^{lam|Z|} ≤ e^{lam Z}+e^{-lam Z}
    have hexpabs : Real.exp (lam * |Z Om|) ≤ Real.exp (lam * Z Om) + Real.exp (-(lam * Z Om)) := by
      rcases abs_cases (Z Om) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he]
        have : (0:ℝ) ≤ Real.exp (-(lam * Z Om)) := (Real.exp_pos _).le
        linarith
      · rw [he]
        have hpos : (0:ℝ) ≤ Real.exp (lam * Z Om) := (Real.exp_pos _).le
        have : lam * -(Z Om) = -(lam * Z Om) := by ring
        rw [this]; linarith
    calc |Z Om| ^ q ≤ (q / (lam * Real.exp 1)) ^ q * Real.exp (lam * |Z Om|) := hstep
      _ ≤ (q / (lam * Real.exp 1)) ^ q *
            (Real.exp (lam * Z Om) + Real.exp (-(lam * Z Om))) := by
          apply mul_le_mul_of_nonneg_left hexpabs (by positivity)
  -- Take bernoulliExpectation: linear with nonneg weights.
  unfold bernoulliExpectation
  have hwnn : ∀ Om : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Om := by
    intro Om; unfold bernoulliObservationWeight
    have : (0:ℝ) ≤ 1 - p := by linarith
    positivity
  -- ∑ w |Z|^q ≤ ∑ w (q/(lam e))^q (e^{lamZ}+e^{-lamZ}) = (q/(lam e))^q (∑w e^{lamZ}+∑w e^{-lamZ})
  calc ∑ Om : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Om * |Z Om| ^ q
      ≤ ∑ Om : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Om *
          ((q / (lam * Real.exp 1)) ^ q *
            (Real.exp (lam * Z Om) + Real.exp (-(lam * Z Om)))) := by
        apply Finset.sum_le_sum
        intro Om _
        exact mul_le_mul_of_nonneg_left (hpoint Om) (hwnn Om)
    _ = (q / (lam * Real.exp 1)) ^ q *
          ((∑ Om : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Om * Real.exp (lam * Z Om))
           + (∑ Om : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Om * Real.exp (-(lam * Z Om)))) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro Om _; ring
    _ ≤ (q / (lam * Real.exp 1)) ^ q * (M + M) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hMGFpos hMGFneg
    _ = 2 * (q / (lam * Real.exp 1)) ^ q * M := by ring
