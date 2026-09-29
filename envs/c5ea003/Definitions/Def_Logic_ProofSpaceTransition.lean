-- Prove2me | Definitions.Def_Logic_ProofSpaceTransition
-- name    : Logic_ProofSpaceTransition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:02:38.118144+00:00
-- url     : https://prove2.me/theorems/7b0a3730-852f-40d4-a870-25691b6881dd
-- title:
--   Aether Catalog definitions — Logic_ProofSpaceTransition
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ProofSpaceTransition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ProofSpaceTransition.lean by skeleton subtraction
import Mathlib

/-!
# A discrete Gödel threshold in finite proof space

This file gives a precise finite model of the proposed phase-transition picture.
At cutoff `n`, `provable n` and `unprovable n` count the two classes of statements
seen so far.  Their difference is the signed order parameter.  The main theorem
shows that, whenever this difference starts positive and ends nonpositive, there
is a unique first cutoff at which the provable majority disappears.  Under a
strict-decrease hypothesis, the sign change is permanent and its location is
unique.

This is deliberately a theorem about an abstract enumeration: incompleteness
alone does not imply any particular asymptotic density or power law without a
choice of syntax, length function, and probability measure.
-/

namespace ProofSpace

/-- The rational proportion of provable statements among all classified statements. -/
def orderParameter (provable unprovable : ℕ) : ℚ :=
  provable / (provable + unprovable)

/-- The signed excess of provable over unprovable statements. -/
def imbalance (provable unprovable : ℕ) : ℤ :=
  (provable : ℤ) - (unprovable : ℤ)

/-- A cutoff is a threshold when its imbalance is nonpositive, but all earlier
cutoffs have positive imbalance. -/
def IsFirstThreshold (f : ℕ → ℤ) (n : ℕ) : Prop :=
  f n ≤ 0 ∧ ∀ m < n, 0 < f m









end ProofSpace


