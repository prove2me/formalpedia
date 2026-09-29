-- Prove2me | solution 1 for RLHF.abs_tiltNorm_sub_quad
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:18:23.72865+00:00
-- url     : https://prove2.me/submissions/00675be0-94f3-46a9-9081-0a51ea121f04

-- Sol generated from Algebra/RLHFKLSecondOrder.lean
import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFKLSecondOrder
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation
import Theorems.Thm_RLHF_abs_sub_mean_le_range
import Theorems.Thm_RLHF_sum_centered
import Theorems.Thm_RLHF_sum_ctr_cube_le
import Theorems.Thm_RLHF_sum_ctr_sq_div

/-!
# The exact second-order KL drift constant is `Var/2`

Domain: Algebra (convex analysis × information theory × alignment theory).

The catalogue's `RLHF.kl_gibbs_le_variance` bounds the alignment KL drift by
`e^{range r/β} Var_p(r)/β²`, i.e. by `Var_p(r)/β²` with an absolute constant `1` in the
large-`β` limit.  The cumulant heuristic predicts that the true constant is `1/2` — the
second cumulant of the tilted family — and this file proves it, quantitatively.

* `RLHF.klDiv_gibbs_eq_centred` — the exact identity
  `KL(π_β‖p) = A_β/W_β − log W_β` with `W_β = 𝔼_p e^{(r−𝔼r)/β}` the centred partition
  function and `A_β = 𝔼_p[e^{(r−𝔼r)/β}·(r−𝔼r)/β]`;
* `RLHF.abs_kl_sub_half_variance` — `|KL(π_β‖p) − Var_p(r)/(2β²)| ≤
  2·range(r)·Var_p(r)/β³ + 3·Var_p(r)²/β⁴` whenever `β ≥ range r`;
* `RLHF.kl_tendsto_half_variance` — hence `β²·KL(π_β‖p) → Var_p(r)/2`.

So the KL drift law is exactly `Var_p(r)/(2β²)`: the variance functional of C1 is
correct for KL (unlike the `ℓ¹` law, whose sharp functional is the mean absolute
deviation, see `Algebra.RLHFMeanAbsoluteDeviation`), and the absolute constant is `1/2`,
half of what the catalogue bound gives.

Combining with Pinsker, `‖π_β − p‖₁ ≤ √(2 KL) ≈ σ_p(r)/β`, which is exactly the
standard-deviation law of C1 — and `RLHF.mad_le_sqrt_variance` shows the true `ℓ¹`
constant `MAD_p(r)` is never larger.  The Pinsker step is therefore the *only* source of
looseness in the σ-law, and its defect is precisely the deviation defect
`σ_p(r) − MAD_p(r)`.

All error terms are third-order Taylor remainders, handled by `Real.exp_bound`.
-/

open RLHF

open Finset

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Centred moment sums -/

omit [Nonempty Ω] in
theorem sum_ctr_div {β : ℝ} {r p : Ω → ℝ} (hp : IsDist p) :
    ∑ y, p y * ((r y - mean p r) / β) = 0 := by
  have h : ∀ y, p y * ((r y - mean p r) / β) = (1 / β) * (p y * (r y - mean p r)) :=
    fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => h y, ← Finset.mul_sum, sum_centered hp r, mul_zero]



/-! ## 2. The centred first moment of the tilt -/





/-! ## 3. The exact KL identity and its second-order expansion -/





open RLHF in
theorem solution{β : ℝ} {r p : Ω → ℝ} (hβ : 0 < β) (hp : IsDist p)
    (hr : rewardRange r ≤ β) :
    |tiltNorm β r p - 1 - variance p r / β ^ 2 / 2|
      ≤ rewardRange r * variance p r / β ^ 3 := by
  have hsmall : ∀ y, |(r y - mean p r) / β| ≤ 1 := by
    intro y
    rw [abs_div, abs_of_pos hβ, div_le_one hβ]
    exact le_trans (abs_sub_mean_le_range hp y) hr
  have hsplit : tiltNorm β r p - 1 - variance p r / β ^ 2 / 2
      = ∑ y, p y * (Real.exp ((r y - mean p r) / β) - 1 - ((r y - mean p r) / β)
          - ((r y - mean p r) / β) ^ 2 / 2) := by
    have h : ∀ y, p y * (Real.exp ((r y - mean p r) / β) - 1 - ((r y - mean p r) / β)
          - ((r y - mean p r) / β) ^ 2 / 2)
        = p y * Real.exp ((r y - mean p r) / β) - p y - p y * ((r y - mean p r) / β)
          - (1 / 2) * (p y * ((r y - mean p r) / β) ^ 2) := fun y => by ring
    rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, sum_ctr_div hp, sum_ctr_sq_div, hp.total]
    simp only [tiltNorm]
    ring
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ y ∈ (univ : Finset Ω),
      |p y * (Real.exp ((r y - mean p r) / β) - 1 - ((r y - mean p r) / β)
        - ((r y - mean p r) / β) ^ 2 / 2)|
      ≤ p y * |(r y - mean p r) / β| ^ 3 := by
    intro y _
    set s := (r y - mean p r) / β with hs
    have hb0 := Real.exp_bound (x := s) (hsmall y) (n := 3) (by norm_num)
    have hsum3 : ∑ m ∈ Finset.range 3, s ^ m / (Nat.factorial m : ℝ)
        = 1 + s + s ^ 2 / 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hsum3] at hb0
    have hb : |Real.exp s - 1 - s - s ^ 2 / 2| ≤ |s| ^ 3 := by
      have hrew : Real.exp s - (1 + s + s ^ 2 / 2) = Real.exp s - 1 - s - s ^ 2 / 2 := by ring
      rw [hrew] at hb0
      refine le_trans hb0 ?_
      have h1 : (0:ℝ) ≤ |s| ^ 3 := by positivity
      have h2 : ((Nat.succ 3 : ℕ) : ℝ) / ((Nat.factorial 3 : ℝ) * ((3 : ℕ) : ℝ)) ≤ 1 := by
        norm_num [Nat.factorial]
      nlinarith [h1, h2]
    rw [abs_mul, abs_of_nonneg (hp.nonneg y)]
    exact mul_le_mul_of_nonneg_left hb (hp.nonneg y)
  exact le_trans (Finset.sum_le_sum hterm) (sum_ctr_cube_le hβ hp)
