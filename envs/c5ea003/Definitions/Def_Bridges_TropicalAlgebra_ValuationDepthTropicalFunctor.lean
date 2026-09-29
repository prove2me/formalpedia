-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_ValuationDepthTropicalFunctor
-- name    : Bridges_TropicalAlgebra_ValuationDepthTropicalFunctor
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:28:33.926664+00:00
-- url     : https://prove2.me/theorems/9084df03-2754-4e8d-86b3-8e1a932194c1
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_ValuationDepthTropicalFunctor
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.ValuationDepthTropicalFunctor`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/ValuationDepthTropicalFunctor.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_CategoricalTropicalUltrametric
/-
  # Valuation-Depth → Tropical Functor (Foundations)

  Bridge: connects valuation-depth complexity measures (the "cost" of building a value
  by repeated combination) to tropical valuation objects (max-plus geometry).

  **Core principle.** A *depth carrier* is a type with a binary combination `add` and a
  depth measure `depth : K → ℕ` obeying the **unit-cost ultrametric law**

      depth (add x y) ≤ max (depth x) (depth y) + 1.

  This is exactly the lax/1-Lipschitz compatibility of `depth` with the tropical addition
  `max` on ℕ, carrying a *unit cost* per combination.  The fundamental quantitative
  theorem (`depth_eval_add_le`) says: for any combination tree `t`, the depth of its
  evaluated value is bounded by the maximal leaf depth *plus the tree height*.  Thus the
  only overhead of repeated combination is the **height** of the combination tree.

  This file is self-contained foundations; follow-up conjectures (C1–C5) live in
  `Catalog/Bridges/ValuationDepthFollowups.lean`.

  -- !-- Lab Notes -- !--
  HYPOTHESIS (PI): the unit-cost law is the *intrinsic* signature of a 1-Lipschitz functor
  from depth carriers to the tropical semiring on ℕ; its overhead on any combination tree
  is governed purely by tree height, and the unit constant `1` is forced.
  EXPERIMENT: formalize `DepthCarrier`, `OpTree`, and prove `depth_eval_add_le` by structural
  induction.  Build the canonical tropical target via the existing `tropicalization_base`.
  ANALYSIS: the induction is clean; height is additive across nodes exactly because each
  node contributes one unit of cost and `max` distributes over the recursive bounds.
  CRITIQUE: ensure the witness attains equality (so the bound is sharp, not vacuous).
  SYNTHESIS: foundations support the C1–C5 follow-ups in the companion file.
-/
namespace ValuationDepthTropical

open CategoricalTropicalUltrametric

/-! ## §1. Depth carriers -/

/-- A **valuation-depth carrier**: a type `K` with a binary combination `add` and a depth
    measure obeying the unit-cost ultrametric law
    `depth (add x y) ≤ max (depth x) (depth y) + 1`. -/
structure DepthCarrier where
  K : Type
  add : K → K → K
  depth : K → ℕ
  depth_add : ∀ x y, depth (add x y) ≤ max (depth x) (depth y) + 1

/-- A depth carrier is **strict** (idempotent / no unit cost) if the depth measure is
    sub-max with *no* `+1` slack: `depth (add x y) ≤ max (depth x) (depth y)`. -/
def IsStrict (X : DepthCarrier) : Prop :=
  ∀ x y, X.depth (X.add x y) ≤ max (X.depth x) (X.depth y)

/-! ## §2. Combination trees -/

/-- Binary combination trees with leaves valued in `K`. -/
inductive OpTree (K : Type) where
  | leaf : K → OpTree K
  | node : OpTree K → OpTree K → OpTree K

namespace OpTree

/-- Evaluate a combination tree under a binary operation. -/
def eval {K : Type} (add : K → K → K) : OpTree K → K
  | leaf k => k
  | node l r => add (eval add l) (eval add r)

/-- Height of a combination tree (a leaf has height `0`). -/
def height {K : Type} : OpTree K → ℕ
  | leaf _ => 0
  | node l r => max (height l) (height r) + 1


/-- Maximal leaf depth of a combination tree under a depth measure. -/
def maxLeafDepth {K : Type} (depth : K → ℕ) : OpTree K → ℕ
  | leaf k => depth k
  | node l r => max (maxLeafDepth depth l) (maxLeafDepth depth r)

end OpTree

/-! ## §3. The fundamental combination-tree bound -/



/-! ## §4. The canonical tropical target and the lax (1-Lipschitz) law -/


/-- The functor's underlying map on points: the depth measure itself. -/
def depthTropMap (X : DepthCarrier) : X.K → ℕ := X.depth


/-! ## §5. The unit-cost witness -/

/-- The canonical **unit-cost operation** on ℕ: `add x y = max x y + 1`.  Every combination
    spends exactly one unit of depth. -/
def unitCostAdd : ℕ → ℕ → ℕ := fun x y => max x y + 1

/-- The **unit-cost witness carrier**: `K = ℕ`, `add = unitCostAdd`, `depth = id`.  The
    unit-cost law holds with *equality*, so it is the extremal carrier. -/
def witnessCarrier : DepthCarrier where
  K := ℕ
  add := unitCostAdd
  depth := id
  depth_add := by intro x y; simp [unitCostAdd]


end ValuationDepthTropical


