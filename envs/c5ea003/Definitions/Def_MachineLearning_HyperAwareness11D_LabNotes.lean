-- Prove2me | Definitions.Def_MachineLearning_HyperAwareness11D_LabNotes
-- name    : MachineLearning_HyperAwareness11D_LabNotes
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:45:11.025737+00:00
-- url     : https://prove2.me/theorems/e6051150-65a3-41b3-997d-0a513630a671
-- title:
--   Aether Catalog definitions — MachineLearning_HyperAwareness11D_LabNotes
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.HyperAwareness11D.LabNotes`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/HyperAwareness11D/LabNotes.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_HyperAwareness11D_FrameBounds

/-!
# Hyper-Awareness — Lab Notes: exact rational experiments in dimension 11

All experiments below are carried out in exact rational arithmetic (`ℚ`), so the printed
numbers are exact, not floating point.  They are the computational evidence that motivated
(and then stress-tested) the theorems of this development; the accompanying file
`ComputationalEvidence.md` reproduces the printed output.

## Experiment 1 — a 21-unit layer collapses two percepts (`collision_21`)

The most natural "almost optimal" architecture on `ℝ¹¹` uses the `11` positive detectors
`x ↦ x_j⁺` and only `10` of the `11` negative detectors.  It has `21` units, one below the
proven optimum `22`.  `collision_21` is a *proof* that the two distinct percepts
`xA = -e₁₀` and `xB = -2 e₁₀` are mapped to the same output, i.e. the missing unit is fatal —
exactly as `HyperAwareness11D.two_mul_le_card_of_injective` predicts.

## Experiment 2 — frame ratios of the optimal 22-unit split layer

`#eval` of `ratio x y = ‖Φx - Φy‖² / ‖x - y‖²` on five percept pairs returns

  `(1/2, 1, 61/102, 1/2, 1)`

confirming the sharp sandwich `1/2 ≤ ratio ≤ 1` of `double_frame`, with the value `1/2`
attained exactly at antipodal pairs and `1` attained against the origin.

## Experiment 3 — activation balance

`#eval` of the pair of active-unit counts `(#active at x, #active at -x)` returns

  `((10, 10), (10, 10), 11, 11)`  (i.e. the pairs `(10,10)`, `(10,10)`, `(11,11)`).

The last percept has all coordinates nonzero (transverse) and gives the perfectly balanced
`11 + 11 = 22` split predicted by `balanced_activation_at_optimum`.  The first two percepts
have a vanishing coordinate, and there the counts drop to `10`: this is precisely why the
theorems quantify over *transverse* probe directions.
-/

namespace HyperAwareness11D.LabNotes

open Finset

/-- Rational ReLU, for exact computation. -/
def reluQ (t : ℚ) : ℚ := max t 0

/-- The `21`-unit layer: all `11` positive detectors, but only `10` negative detectors. -/
def W21 : Fin 21 → Fin 11 → ℚ := fun i j =>
  if (i : ℕ) < 11 then (if (i : ℕ) = (j : ℕ) then 1 else 0)
  else (if (i : ℕ) - 11 = (j : ℕ) then -1 else 0)

/-- The layer map of `W21`. -/
def layer21 (x : Fin 11 → ℚ) : Fin 21 → ℚ := fun i => reluQ (∑ j, W21 i j * x j)

def xA : Fin 11 → ℚ := fun j => if (j : ℕ) = 10 then -1 else 0
def xB : Fin 11 → ℚ := fun j => if (j : ℕ) = 10 then -2 else 0







-- Experiment 2: prints `(1/2, 1, 61/102, 1/2, 1)`

-- Experiment 3: prints `((10, 10), (10, 10), 11, 11)`
end HyperAwareness11D.LabNotes


