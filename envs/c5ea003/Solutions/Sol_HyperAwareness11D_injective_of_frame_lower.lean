-- Prove2me | solution 1 for HyperAwareness11D.injective_of_frame_lower
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:26:25.27059+00:00
-- url     : https://prove2.me/submissions/91baa2a1-200c-4212-9cdd-f245f2f528d4

-- Sol generated from MachineLearning/HyperAwareness11D/FrameBounds.lean
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_FrameBounds
import Definitions.Def_MachineLearning_HyperAwareness11D_Injectivity
import Theorems.Thm_HyperAwareness11D_preAct_doubleW_inl
import Theorems.Thm_HyperAwareness11D_preAct_doubleW_inr
import Theorems.Thm_HyperAwareness11D_relu_pair_sandwich

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


lemma sqdist_nonneg [Fintype ι] (x y : ι → ℝ) : 0 ≤ sqdist x y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## The coordinatewise sandwich -/


/-! ## The frame bounds for the optimal layer -/

lemma sqdist_double_eq (x y : Fin n → ℝ) :
    sqdist (reluLayer (doubleW n) 0 x) (reluLayer (doubleW n) 0 y)
      = ∑ i : Fin n, ((relu (x i) - relu (y i)) ^ 2 + (relu (-x i) - relu (-y i)) ^ 2) := by
  rw [sqdist, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [reluLayer, preAct_doubleW_inl, preAct_doubleW_inr]


/-- **Frame bounds (lower).**  The optimal `2n`-unit layer expands squared distances by at
least `1/2`: the 11-dimensional percept is recoverable with condition number `√2`. -/
theorem double_frame_lower (x y : Fin n → ℝ) :
    sqdist x y / 2 ≤ sqdist (reluLayer (doubleW n) 0 x) (reluLayer (doubleW n) 0 y) := by
  rw [sqdist_double_eq, sqdist, Finset.sum_div]
  refine Finset.sum_le_sum ?_
  intro i _
  exact (relu_pair_sandwich (x i) (y i)).1



/-! ## Sharpness of both constants in dimension 11 -/






/-! ## A general contraction estimate -/




open HyperAwareness11D in
theorem solution:
    Function.Injective (reluLayer (doubleW n) 0) := by
  intro x y hxy
  have h := double_frame_lower x y
  have hzero : sqdist (reluLayer (doubleW n) 0 x) (reluLayer (doubleW n) 0 y) = 0 := by
    rw [hxy]; simp [sqdist]
  rw [hzero] at h
  have hs : sqdist x y ≤ 0 := by linarith
  have hnn : (0:ℝ) ≤ sqdist x y := sqdist_nonneg x y
  have heq : sqdist x y = 0 := le_antisymm hs hnn
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i - y i))).mp heq i
    (Finset.mem_univ i)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith [this]
