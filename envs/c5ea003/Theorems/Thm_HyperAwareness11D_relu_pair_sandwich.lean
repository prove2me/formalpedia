-- Prove2me | Theorems.Thm_HyperAwareness11D_relu_pair_sandwich
-- name    : HyperAwareness11D.relu_pair_sandwich
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:38:15.950598+00:00
-- url     : https://prove2.me/theorems/cc95603b-d66d-4951-bc28-a216ef464129
-- title:
--   The heart of the frame estimate: for a single coordinate, the pair
-- statement:
--   The heart of the frame estimate: for a single coordinate, the pair
--   `(relu a - relu b, relu (-a) - relu (-b))` has squared length between `(a-b)²/2` and `(a-b)²`.
--   The lower bound is the Cauchy–Schwarz inequality `(u - v)² ≤ 2(u² + v²)` applied to the
--   identity `(relu a - relu b) - (relu (-a) - relu (-b)) = a - b`; the upper bound holds because
--   the two coordinates always move in opposite directions.
--
--   ```lean
--   theorem HyperAwareness11D.relu_pair_sandwich(a b : ℝ) :
--       (a - b) ^ 2 / 2 ≤ (relu a - relu b) ^ 2 + (relu (-a) - relu (-b)) ^ 2 ∧
--         (relu a - relu b) ^ 2 + (relu (-a) - relu (-b)) ^ 2 ≤ (a - b) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/HyperAwareness11D/FrameBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/HyperAwareness11D/FrameBounds.lean#L39

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

theorem HyperAwareness11D.relu_pair_sandwich(a b : ℝ) :
    (a - b) ^ 2 / 2 ≤ (relu a - relu b) ^ 2 + (relu (-a) - relu (-b)) ^ 2 ∧
      (relu a - relu b) ^ 2 + (relu (-a) - relu (-b)) ^ 2 ≤ (a - b) ^ 2 := by sorry
