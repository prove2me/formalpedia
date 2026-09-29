-- Prove2me | Definitions.Def_Bridges_ThresholdPhaseTransition
-- name    : Bridges_ThresholdPhaseTransition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:46.508336+00:00
-- url     : https://prove2.me/theorems/0f3aa460-8009-4451-8a95-e7f35e3ff439
-- title:
--   Aether Catalog definitions — Bridges_ThresholdPhaseTransition
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ThresholdPhaseTransition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ThresholdPhaseTransition.lean by skeleton subtraction
import Mathlib
/-
# Binary Search Threshold for Global Minimizers

This file formalizes a **phase transition theorem** for marking-bonus perturbations
over finite search spaces. Given a finite type `O`, a cost function `cost : O → ℝ`,
and a marking predicate `marked : O → Prop`, we define the β-perturbed objective

    F_β(x) := cost(x) - β · 𝟙_{marked(x)}

and prove that there is a sharp threshold `Δ = markedMin - globalMin` such that:
- For β < Δ, every minimizer of F_β is unmarked.
- For β > Δ, every minimizer of F_β is marked.
- At β = Δ, both marked and unmarked minimizers coexist.

This is a formal **bifurcation theorem** with applications in optimization,
tropical geometry (wall-crossing), statistical mechanics (phase transitions),
and certified search (binary search on the bonus parameter).

## Cross-domain connections

- **Tropical geometry**: The threshold Δ is the intersection of two tropical
  affine branches: the unmarked branch (constant in β) and the marked branch
  (slope -1). This is a wall-crossing event.

- **Statistical mechanics**: β acts as an external field; the theorem formalizes
  a zero-temperature phase transition in a finite energy landscape.

- **Machine learning / reward shaping**: A reward bonus changes the optimizer
  exactly when the bonus exceeds the value gap.

- **Certified search**: Binary search on β recovers the marked optimum value
  without solving a constrained optimization problem each time.
-/


open Classical

/-! ## Core definitions -/

/-- The β-perturbed objective: `cost(x) - β` if `x` is marked, `cost(x)` otherwise. -/
noncomputable def bonusObj {O : Type*} [Fintype O] (cost : O → ℝ) (marked : O → Prop)
    [DecidablePred marked] (β : ℝ) (x : O) : ℝ :=
  cost x - if marked x then β else 0

/-- A point `x` is a global minimizer of `f` if `f(x) ≤ f(y)` for all `y`. -/
def IsGlobalMin {O : Type*} (f : O → ℝ) (x : O) : Prop :=
  ∀ y, f x ≤ f y


/-! ## Helper lemmas about bonusObj -/



/-! ## Existence of minimizers -/

/-
Every nonempty finite type has a global minimizer for any real-valued function.
-/

/-
Among marked points, there exists a cost-minimizing one.
-/

/-! ## Main threshold theorem -/

/-
**Main Threshold Theorem (strict phases).**
Given a global minimizer `x₀` and a marked minimizer `xm`, the gap `Δ = cost(xm) - cost(x₀)`
is the critical threshold:
- For β < Δ, every minimizer of the perturbed objective is unmarked.
- For β > Δ, every minimizer of the perturbed objective is marked.
-/

/-! ## Bifurcation at the critical value -/

/-
At the critical value `Δ = cost(xm) - cost(x₀)`, the perturbed objectives
of `x₀` (unmarked) and `xm` (marked) are tied.
-/

/-
At the critical value, both `x₀` and `xm` are global minimizers of the perturbed objective.
This is the **bifurcation theorem**: marked and unmarked minimizers coexist at the threshold.
-/

/-! ## Monotonicity of "all minimizers are marked" -/

/-
The predicate "every minimizer of F_β is marked" is monotone in β:
if it holds at β, it holds for all γ ≥ β.
-/

/-! ## Existential threshold theorem -/

/-
**Existential Threshold Theorem.**
Under the assumption that there exist marked points and an unmarked global minimizer,
there exists a critical threshold `Δ ≥ 0` with the strict phase separation property.
-/

/-! ## Tropical decomposition identity -/

/-
The global minimum of the perturbed objective decomposes as the minimum of
the unmarked minimum and the marked minimum minus β.
This is the **tropical normal form**: two affine branches in β.
-/


