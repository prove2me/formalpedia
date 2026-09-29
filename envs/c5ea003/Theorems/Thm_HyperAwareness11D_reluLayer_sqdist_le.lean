-- Prove2me | Theorems.Thm_HyperAwareness11D_reluLayer_sqdist_le
-- name    : HyperAwareness11D.reluLayer_sqdist_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:38:44.808252+00:00
-- url     : https://prove2.me/theorems/257c5e6d-dc37-470e-88da-1c4354e8d04b
-- title:
--   Every ReLU layer contracts distances relative to its own linear part; this is why the
-- statement:
--   Every ReLU layer contracts distances relative to its own linear part; this is why the
--   upper frame constant of the optimal layer can be as small as `1`.
--
--   ```lean
--   theorem HyperAwareness11D.reluLayer_sqdist_le[Fintype ι] (W : ι → Fin n → ℝ) (b : ι → ℝ) (x y : Fin n → ℝ) :
--       sqdist (reluLayer W b x) (reluLayer W b y) ≤ ∑ i, (preAct W b x i - preAct W b y i) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HyperAwareness11D/FrameBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HyperAwareness11D/FrameBounds.lean#L144

-- Thm stub generated from MachineLearning/HyperAwareness11D/FrameBounds.lean
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

theorem HyperAwareness11D.reluLayer_sqdist_le[Fintype ι] (W : ι → Fin n → ℝ) (b : ι → ℝ) (x y : Fin n → ℝ) :
    sqdist (reluLayer W b x) (reluLayer W b y) ≤ ∑ i, (preAct W b x i - preAct W b y i) ^ 2 := by sorry
