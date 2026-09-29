-- Prove2me | Theorems.Thm_HyperAwareness11D_injective_of_frame_lower
-- name    : HyperAwareness11D.injective_of_frame_lower
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:38:52.72571+00:00
-- url     : https://prove2.me/theorems/268b8ed3-a02e-47a9-917d-1ef8eb1cbb72
-- title:
--   A frame lower bound immediately re-proves injectivity, independently of the
-- statement:
--   A frame lower bound immediately re-proves injectivity, independently of the
--   combinatorial argument in `Injectivity.lean`.
--
--   ```lean
--   theorem HyperAwareness11D.injective_of_frame_lower:
--       Function.Injective (reluLayer (doubleW n) 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HyperAwareness11D/FrameBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HyperAwareness11D/FrameBounds.lean#L94

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

theorem HyperAwareness11D.injective_of_frame_lower:
    Function.Injective (reluLayer (doubleW n) 0) := by sorry
