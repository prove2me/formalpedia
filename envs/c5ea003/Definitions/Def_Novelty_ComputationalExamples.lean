-- Prove2me | Definitions.Def_Novelty_ComputationalExamples
-- name    : Novelty_ComputationalExamples
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:09:58.296338+00:00
-- url     : https://prove2.me/theorems/92753f6a-501f-4031-90a7-916758d9fa30
-- title:
--   Aether Catalog definitions — Novelty_ComputationalExamples
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ComputationalExamples`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ComputationalExamples.lean by skeleton subtraction
import Mathlib

/-!
# Certified small activation-pattern calculations

These self-contained examples expose the key correction to the naive `2^k`
claim. Two gates can realize all four patterns, but two perfectly correlated
gates realize only two feasible patterns.
-/

open Function Set

namespace ActivationStoneExamples

abbrev Pattern (k : ℕ) := Fin k → Bool
def Feasible {X : Type*} {k : ℕ} (a : X → Pattern k) := Set.range a

/-- Two independent gates, with the pattern itself as input. -/
def independentTwo : Pattern 2 → Pattern 2 := id

/-- Two duplicated gates: both copy the same Boolean input. -/
def duplicatedTwo (b : Bool) : Pattern 2 := fun _ => b

/-
Independent two-gate activations realize all four formal patterns.
-/

/-
Duplicated gates realize only the all-false and all-true patterns.
-/

/-
Thus the unconditional assertion that two gates always yield four Stone
points is false.
-/

/-
For zero gates there is one formal pattern and every nonempty input type
realizes it.
-/

end ActivationStoneExamples


