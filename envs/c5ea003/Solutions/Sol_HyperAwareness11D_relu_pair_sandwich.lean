-- Prove2me | solution 1 for HyperAwareness11D.relu_pair_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:24:34.241359+00:00
-- url     : https://prove2.me/submissions/3e38db94-b820-478f-bfe9-97d26fa64094

-- Sol generated from MachineLearning/HyperAwareness11D/FrameBounds.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_FrameBounds
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity
import Theorems.Thm_HyperAwareness11D_relu_of_nonneg
import Theorems.Thm_HyperAwareness11D_relu_of_nonpos

/-!
# Hyper-Awareness II: metric stability of the optimal 11-dimensional perception layer

`MachineLearning.HyperAwareness11D.Injectivity` shows that `22` units are necessary **and**
sufficient for a ReLU layer on `ℝ¹¹` to be injective, the optimum being realised by the
positive/negative split layer `Φ x = (x⁺, x⁻)`.

Injectivity alone is a set-theoretic statement: it does not by itself guarantee that the
percept can be *stably* recovered.  Here we upgrade it to a quantitative statement: the
optimal layer is a **frame** with sharp constants

  `(1/2) ‖x - y‖² ≤ ‖Φ x - Φ y‖² ≤ ‖x - y‖²`,

so the 11-dimensional percept is recovered with condition number exactly `√2`, uniformly
over all inputs.  Both constants are attained (`double_frame_upper_sharp`,
`double_frame_lower_sharp`), so no better bi-Lipschitz estimate exists for this layer.

We also record the general fact that *every* ReLU layer is contractive relative to its own
linear part (`reluLayer_sqdist_le`), which is what makes the upper bound `1` possible.
-/

open HyperAwareness11D

open Finset

noncomputable section

variable {ι : Type*} {n : ℕ}



/-! ## The coordinatewise sandwich -/


/-! ## The frame bounds for the optimal layer -/






/-! ## Sharpness of both constants in dimension 11 -/






/-! ## A general contraction estimate -/




open HyperAwareness11D in
theorem solution(a b : ℝ) :
    (a - b) ^ 2 / 2 ≤ (relu a - relu b) ^ 2 + (relu (-a) - relu (-b)) ^ 2 ∧
      (relu a - relu b) ^ 2 + (relu (-a) - relu (-b)) ^ 2 ≤ (a - b) ^ 2 := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [relu_of_nonpos ha, relu_of_nonpos hb, relu_of_nonneg (neg_nonneg.mpr ha),
      relu_of_nonneg (neg_nonneg.mpr hb)]
    constructor <;> nlinarith [sq_nonneg (a - b)]
  · rw [relu_of_nonpos ha, relu_of_nonneg hb, relu_of_nonneg (neg_nonneg.mpr ha),
      relu_of_nonpos (neg_nonpos.mpr hb)]
    constructor <;> nlinarith [sq_nonneg (a + b), mul_nonneg (neg_nonneg.mpr ha) hb]
  · rw [relu_of_nonneg ha, relu_of_nonpos hb, relu_of_nonpos (neg_nonpos.mpr ha),
      relu_of_nonneg (neg_nonneg.mpr hb)]
    constructor <;> nlinarith [sq_nonneg (a + b), mul_nonneg ha (neg_nonneg.mpr hb)]
  · rw [relu_of_nonneg ha, relu_of_nonneg hb, relu_of_nonpos (neg_nonpos.mpr ha),
      relu_of_nonpos (neg_nonpos.mpr hb)]
    constructor <;> nlinarith [sq_nonneg (a - b)]
