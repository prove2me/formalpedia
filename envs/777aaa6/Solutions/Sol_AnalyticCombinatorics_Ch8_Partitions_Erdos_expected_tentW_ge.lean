-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.expected_tentW_ge
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T12:02:53.532992+00:00
-- url     : https://prove2.me/submissions/7ff099ad-8050-4747-a537-30522adeca10

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_TentDefect
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# The tent / defect function `Φ_W(d) = max(|d| − W, 0)` (renewal route B primitives)

The fixed-window Tanaka-DEFECT route to the renewal limit uses `Φ_W(d) = max(|d| − W, 0)`: it counts
window crossings robustly to the soft far jumps that break the plain window-occupation local time
(route A is dead — fixed-`b` truncation removes constant mass; see `DOCTRINE-walls.md`).

This file banks the certain primitives:
* `tentW_nonneg`, `tentW_ge` (`Φ_W d ≥ |d| − W`, the PZ-transfer with a `−W` loss),
* `tentW_le_abs`, `tentW_lipschitz`,
* `expected_tentW_ge` (`E[Φ_W(D)] ≥ E|D| − W`), turning the banked `E|D_T| ≥ c√T` into growth of the
  defect potential.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {ι : Type*} [Fintype ι]

@[simp] lemma tentW_nonneg (W d : ℝ) : 0 ≤ tentW W d := le_max_right _ _

/-- The PZ-transfer inequality: `Φ_W d ≥ |d| − W`. -/
lemma tentW_ge (W d : ℝ) : |d| - W ≤ tentW W d := le_max_left _ _

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
variable {ι : Type*} [Fintype ι]
theorem solution (W : ℝ) (D : ι → ℝ) (μ : ι → ℝ)
    (hμsum : ∑ x, μ x = 1) (hμnn : ∀ x, 0 ≤ μ x) :
    (∑ x, μ x * |D x|) - W ≤ ∑ x, μ x * tentW W (D x) := by
  have hstep : (∑ x, μ x * (|D x| - W)) = (∑ x, μ x * |D x|) - W := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hμsum, one_mul]
  rw [← hstep]
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (tentW_ge W (D x)) (hμnn x))
