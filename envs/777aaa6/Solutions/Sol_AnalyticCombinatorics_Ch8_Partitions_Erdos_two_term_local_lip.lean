-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.two_term_local_lip
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:10:35.356251+00:00
-- url     : https://prove2.me/submissions/a8915f7e-60c9-427c-8b31-3df8f9c4b5e3

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: two-term expansion ⟹ local Lipschitz (η ~ 1/r²)

⚠ DRAFT — written WITHOUT a local build (server down); queued for batch verification on uisai1 recovery.

Modular bridge from the smooth-rank mean-decrement two-term expansion `f n = c₀ + c₁/√n + O(1/n)` to the
approximate-martingale bound `|f x − f y| ≤ K'/x` for comparable starts (`|√x − √y| ≤ W0`).  The constant
`c₀` cancels; `|c₁/√x − c₁/√y| = O(W0/x)` (since `√x√y ≥ x/2` for large `x`); the two `O(1/n)` remainders
are `O(1/x)` (since `y ≥ x/4`).  Hence `|f x − f y| ≤ (5K + 2|c₁|W0)/x = O(1/r²)`, `r = 3√x`.  Consumes the
(still-to-prove) two-term Lambert-moment expansion as a hypothesis.  Opus-authored.
-/

noncomputable section

open Filter Topology

end

open Filter Topology
theorem solution (f : ℕ → ℝ) (c₀ c₁ K W0 : ℝ) (hK : 0 ≤ K) (hW0 : 0 ≤ W0)
    (hexp : ∀ᶠ n : ℕ in atTop, |f n - (c₀ + c₁ / Real.sqrt (n : ℝ))| ≤ K / (n : ℝ)) :
    ∃ K' R0 : ℝ, 0 < K' ∧ ∀ x y : ℕ, R0 ≤ (x : ℝ) → R0 ≤ (y : ℝ) →
      |Real.sqrt (x : ℝ) - Real.sqrt (y : ℝ)| ≤ W0 → |f x - f y| ≤ K' / (x : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hexp
  refine ⟨5 * K + 2 * |c₁| * W0 + 1, max (N : ℝ) ((2 * W0) ^ 2 + 1), by positivity, ?_⟩
  intro x y hx hy hcomp
  have hxN : N ≤ x := by exact_mod_cast le_trans (le_max_left _ _) hx
  have hyN : N ≤ y := by exact_mod_cast le_trans (le_max_left _ _) hy
  have hxbig : (2 * W0) ^ 2 + 1 ≤ (x : ℝ) := le_trans (le_max_right _ _) hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by nlinarith [sq_nonneg (2 * W0), hxbig]
  have hsx : 0 < Real.sqrt (x : ℝ) := Real.sqrt_pos.2 hxpos
  -- √x > 2 W0
  have h2W0 : (0 : ℝ) ≤ 2 * W0 := by positivity
  have hsxbig : 2 * W0 < Real.sqrt (x : ℝ) := by
    rw [show (2 * W0) = Real.sqrt ((2 * W0) ^ 2) from (Real.sqrt_sq h2W0).symm]
    exact Real.sqrt_lt_sqrt (by positivity) (by linarith [hxbig])
  rcases abs_le.1 hcomp with ⟨hlo, hhi⟩
  -- √y ≥ √x − W0 ≥ √x/2 > 0
  have hsy_lb : Real.sqrt (x : ℝ) / 2 ≤ Real.sqrt (y : ℝ) := by linarith [hhi, hsxbig]
  have hsy : 0 < Real.sqrt (y : ℝ) := by linarith [hsy_lb, hsx]
  -- x/2 ≤ √x √y
  have hprod : (x : ℝ) / 2 ≤ Real.sqrt (x : ℝ) * Real.sqrt (y : ℝ) := by
    nlinarith [hsy_lb, hsx, Real.sq_sqrt hxpos.le]
  -- x/4 ≤ y, so K/y ≤ 4K/x  (here y > 0)
  have hypos : (0 : ℝ) < (y : ℝ) := by
    have h1y : (1 : ℝ) ≤ (y : ℝ) :=
      le_trans (le_trans (by nlinarith [sq_nonneg (2 * W0)] : (1:ℝ) ≤ (2 * W0) ^ 2 + 1)
        (le_max_right (N : ℝ) _)) hy
    linarith
  have hy4 : (x : ℝ) / 4 ≤ (y : ℝ) := by
    have : (Real.sqrt (x : ℝ) / 2) ^ 2 ≤ (Real.sqrt (y : ℝ)) ^ 2 := by
      have h0 : (0 : ℝ) ≤ Real.sqrt (x : ℝ) / 2 := by positivity
      nlinarith [hsy_lb, h0]
    rw [Real.sq_sqrt hypos.le] at this
    nlinarith [Real.sq_sqrt hxpos.le, this]
  -- the three pieces
  have hfx : |f x - (c₀ + c₁ / Real.sqrt (x : ℝ))| ≤ K / (x : ℝ) := hN x hxN
  have hfy : |f y - (c₀ + c₁ / Real.sqrt (y : ℝ))| ≤ K / (y : ℝ) := hN y hyN
  have hKy : K / (y : ℝ) ≤ 4 * K / (x : ℝ) := by
    rw [div_le_div_iff₀ hypos hxpos]; nlinarith [hy4, hK]
  -- |c₁/√x − c₁/√y| ≤ |c₁| · 2 W0 / x
  have hmid : |c₁ / Real.sqrt (x : ℝ) - c₁ / Real.sqrt (y : ℝ)| ≤ |c₁| * (2 * W0) / (x : ℝ) := by
    have heq : c₁ / Real.sqrt (x : ℝ) - c₁ / Real.sqrt (y : ℝ)
        = c₁ * (Real.sqrt (y : ℝ) - Real.sqrt (x : ℝ)) / (Real.sqrt (x : ℝ) * Real.sqrt (y : ℝ)) := by
      field_simp
    rw [heq, abs_div, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ Real.sqrt (x:ℝ) * Real.sqrt (y:ℝ) by positivity)]
    rw [div_le_div_iff₀ (by positivity) hxpos]
    have hnum : |Real.sqrt (y : ℝ) - Real.sqrt (x : ℝ)| ≤ W0 := by
      rw [abs_sub_comm]; exact hcomp
    have h_a := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (abs_nonneg c₁)) hxpos.le
    have h_b := mul_le_mul_of_nonneg_left hprod (by positivity : (0:ℝ) ≤ 2 * |c₁| * W0)
    nlinarith [h_a, h_b]
  -- assemble via triangle inequality
  have htri : |f x - f y|
      ≤ |f x - (c₀ + c₁ / Real.sqrt (x : ℝ))|
        + |c₁ / Real.sqrt (x : ℝ) - c₁ / Real.sqrt (y : ℝ)|
        + |f y - (c₀ + c₁ / Real.sqrt (y : ℝ))| := by
    have h1 : |f x - f y|
        ≤ |f x - (c₀ + c₁ / Real.sqrt (x : ℝ))| + |(c₀ + c₁ / Real.sqrt (x : ℝ)) - f y| :=
      abs_sub_le _ _ _
    have h2 : |(c₀ + c₁ / Real.sqrt (x : ℝ)) - f y|
        ≤ |(c₀ + c₁ / Real.sqrt (x : ℝ)) - (c₀ + c₁ / Real.sqrt (y : ℝ))|
          + |(c₀ + c₁ / Real.sqrt (y : ℝ)) - f y| := abs_sub_le _ _ _
    have h3 : |(c₀ + c₁ / Real.sqrt (x : ℝ)) - (c₀ + c₁ / Real.sqrt (y : ℝ))|
        = |c₁ / Real.sqrt (x : ℝ) - c₁ / Real.sqrt (y : ℝ)| := by
      rw [show (c₀ + c₁ / Real.sqrt (x:ℝ)) - (c₀ + c₁ / Real.sqrt (y:ℝ))
        = c₁ / Real.sqrt (x:ℝ) - c₁ / Real.sqrt (y:ℝ) by ring]
    have h4 : |(c₀ + c₁ / Real.sqrt (y : ℝ)) - f y| = |f y - (c₀ + c₁ / Real.sqrt (y : ℝ))| :=
      abs_sub_comm _ _
    linarith [h1, h2, h3, h4]
  have hmid' : |c₁ / Real.sqrt (x : ℝ) - c₁ / Real.sqrt (y : ℝ)| ≤ 2 * |c₁| * W0 / (x : ℝ) := by
    rw [show 2 * |c₁| * W0 / (x:ℝ) = |c₁| * (2 * W0) / (x:ℝ) by ring]; exact hmid
  calc |f x - f y| ≤ K / (x:ℝ) + 2 * |c₁| * W0 / (x:ℝ) + K / (y:ℝ) := by
        linarith [htri, hfx, hfy, hmid']
    _ ≤ K / (x:ℝ) + 2 * |c₁| * W0 / (x:ℝ) + 4 * K / (x:ℝ) := by linarith [hKy]
    _ ≤ (5 * K + 2 * |c₁| * W0 + 1) / (x:ℝ) := by
        rw [← add_div, ← add_div, div_le_div_iff₀ hxpos hxpos]
        nlinarith [hxpos, hK, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (abs_nonneg c₁)) hW0]
