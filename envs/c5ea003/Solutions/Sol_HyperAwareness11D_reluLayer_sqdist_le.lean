-- Prove2me | solution 1 for HyperAwareness11D.reluLayer_sqdist_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:28:30.045985+00:00
-- url     : https://prove2.me/submissions/d9016bda-d145-48ae-b22f-df7111c84476

-- Sol generated from MachineLearning/HyperAwareness11D/FrameBounds.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_FrameBounds
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity

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
theorem solution[Fintype ι] (W : ι → Fin n → ℝ) (b : ι → ℝ) (x y : Fin n → ℝ) :
    sqdist (reluLayer W b x) (reluLayer W b y) ≤ ∑ i, (preAct W b x i - preAct W b y i) ^ 2 := by
  refine Finset.sum_le_sum ?_
  intro i _
  have h : |relu (preAct W b x i) - relu (preAct W b y i)|
      ≤ |preAct W b x i - preAct W b y i| := by
    simp only [relu]
    exact abs_max_sub_max_le_abs _ _ _
  calc (relu (preAct W b x i) - relu (preAct W b y i)) ^ 2
      = |relu (preAct W b x i) - relu (preAct W b y i)| ^ 2 := (sq_abs _).symm
    _ ≤ |preAct W b x i - preAct W b y i| ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (preAct W b x i - preAct W b y i) ^ 2 := sq_abs _
