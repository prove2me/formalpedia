-- Prove2me | solution 1 for markov_polya_grid
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-09T02:36:16.20019+00:00
-- url     : https://prove2.me/submissions/99bd897b-378f-4371-a523-c68e000b32e6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_markov_polya_grid
import Theorems.Thm_polynomial_grid_continuous_extension
import Theorems.Thm_markov_inequality_interval
import Mathlib.Tactic.Linarith

/-!
# Sketch — `markov_polya_grid`

Decompose the integer-grid Markov inequality into:

1. **Sharp continuous extension** (`polynomial_grid_continuous_extension`):
   in the regime `2 d² ≤ b`, the integer-grid bound `|Q(j)| ≤ 1` propagates
   to the continuous bound `|Q(x)| ≤ 1` on `[0, b]`.
2. **Classical Markov on `[0, b]`** (`markov_inequality_interval`):
   for poly bounded by `M` on continuous `[a, b]`, `|Q'(c)| ≤ 2 d² M / (b-a)`.

Combining (with `M = 1`, `a = 0`, `b = b`): `|Q'(c)| ≤ 2 d² / b` on `[0, b]`.
-/

theorem solution
    {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ}
    (h_deg : Q.natDegree ≤ d)
    (h_bound : ∀ t : ℕ, t ≤ b → |Q.eval (t : ℝ)| ≤ 1)
    (h_regime : 2 * d^2 ≤ b) :
    ∀ c : ℝ, 0 ≤ c → c ≤ (b : ℝ) →
      |Q.derivative.eval c| ≤ 2 * (d : ℝ)^2 / (b : ℝ) := by
  intros c hc_ge hc_le
  -- Step 1: continuous bound from integer grid
  have h_cont : ∀ x : ℝ, 0 ≤ x → x ≤ (b : ℝ) → |Q.eval x| ≤ 1 :=
    polynomial_grid_continuous_extension Q h_deg h_bound h_regime
  -- Step 2: Markov on [0, b]
  have hb_pos_real : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have h_markov := markov_inequality_interval 0 (b : ℝ) hb_pos_real Q 1 h_deg
                    (fun x hx_ge hx_le => h_cont x hx_ge hx_le) c hc_ge hc_le
  -- Tidy up the bound: 2 * d² * 1 / (b - 0) = 2 d² / b
  have h_eq : 2 * (d : ℝ)^2 * 1 / ((b : ℝ) - 0) = 2 * (d : ℝ)^2 / (b : ℝ) := by
    rw [mul_one, sub_zero]
  linarith [h_eq ▸ h_markov]
