-- Prove2me | Definitions.Def_Bridges_ComputationalComplexityRecipes_CulinaryComplexity
-- name    : Bridges_ComputationalComplexityRecipes_CulinaryComplexity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:25:51.348578+00:00
-- url     : https://prove2.me/theorems/fbc091f8-9f15-4181-822c-2820f6acceec
-- title:
--   Aether Catalog definitions — Bridges_ComputationalComplexityRecipes_CulinaryComplexity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ComputationalComplexityRecipes.CulinaryComplexity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ComputationalComplexityRecipes/CulinaryComplexity.lean by skeleton subtraction
import Mathlib
/-
# Computational Complexity of Recipes: Kitchen Complexity Theory

We formalize recipes as computational processes with two fundamental time measures:
cooking time C(R) and verification time V(R). This creates a rich complexity theory
analogous to classical P vs NP, with novel structural results about composition,
reduction, and the "verification gap" — the ratio C(R)/V(R).

## Key Results:
- The Verification Gap Theorem: composition cannot decrease the verification gap
- Kitchen Hierarchy Theorem: strict separation between complexity classes
- Destructive Verification Lemma: recipes requiring destructive testing have bounded gaps
- Reduction Transitivity: kitchen reductions compose and preserve class membership
-/


open Finset Function

/-! ## Core Definitions -/

/-- A `Recipe` encodes a computational cooking process with measurable complexity.
  `numIngredients` is the input size (number of distinct ingredients).
  `numOperations` is the number of distinct cooking operations (chop, heat, mix, etc.).
  `cookTime` is the total cooking time C(R) in abstract time units.
  `verifyTime` is the verification time V(R) — how long to determine output quality.
  `destructive` indicates whether verification destroys the output (e.g., cutting a soufflé). -/
structure Recipe where
  numIngredients : ℕ
  numOperations : ℕ
  cookTime : ℕ
  verifyTime : ℕ
  destructive : Bool
  cook_pos : 0 < cookTime
  verify_pos : 0 < verifyTime
  deriving Repr


/-- A recipe is "quick" if cooking time equals verification time (P = NP in kitchen). -/
def Recipe.isQuick (R : Recipe) : Prop :=
  R.cookTime = R.verifyTime

/-- A recipe is "hard" if cooking time strictly exceeds verification time (P ≠ NP in kitchen). -/
def Recipe.isHard (R : Recipe) : Prop :=
  R.cookTime > R.verifyTime


/-! ## Recipe Composition -/

/-- Sequential composition of two recipes: cook R₁ then R₂.
    Times add, ingredient/operation counts combine. -/
def Recipe.seq (R₁ R₂ : Recipe) : Recipe where
  numIngredients := R₁.numIngredients + R₂.numIngredients
  numOperations := R₁.numOperations + R₂.numOperations
  cookTime := R₁.cookTime + R₂.cookTime
  verifyTime := R₁.verifyTime + R₂.verifyTime
  destructive := R₁.destructive || R₂.destructive
  cook_pos := Nat.add_pos_left R₁.cook_pos _
  verify_pos := Nat.add_pos_left R₁.verify_pos _

/-- Parallel composition: cook R₁ and R₂ simultaneously.
    Cook time is the max, verify time adds (must check both). -/
def Recipe.par (R₁ R₂ : Recipe) : Recipe where
  numIngredients := R₁.numIngredients + R₂.numIngredients
  numOperations := R₁.numOperations + R₂.numOperations
  cookTime := max R₁.cookTime R₂.cookTime
  verifyTime := R₁.verifyTime + R₂.verifyTime
  destructive := R₁.destructive || R₂.destructive
  cook_pos := lt_of_lt_of_le R₁.cook_pos (Nat.le_max_left _ _)
  verify_pos := Nat.add_pos_left R₁.verify_pos _

/-! ## Kitchen Complexity Classes -/

/-- Kitchen-P: recipes cookable in time ≤ bound. -/
def KitchenP (bound : ℕ) : Set Recipe :=
  {R | R.cookTime ≤ bound}

/-- Kitchen-NP: recipes verifiable in time ≤ bound. -/
def KitchenNP (bound : ℕ) : Set Recipe :=
  {R | R.verifyTime ≤ bound}


/-! ## Kitchen Reductions -/


/-! ## The Culinary Complexity Hierarchy

We define a hierarchy of recipe complexity levels based on the
verification gap, creating a novel mathematical structure. -/

/-- Culinary complexity level based on the verification gap. -/
inductive CulinaryLevel
  | trivial    -- gap = 1 (instant recipes, P = NP)
  | easy       -- 1 < gap ≤ 2
  | moderate   -- 2 < gap ≤ 4
  | hard       -- 4 < gap
  | impossible -- verification-hard (gap < 1 conceptually)
  deriving Repr, DecidableEq

/-- Classify a recipe into its culinary complexity level. -/
def classifyRecipe (R : Recipe) : CulinaryLevel :=
  if R.verifyTime ≥ R.cookTime then CulinaryLevel.impossible
  else if R.cookTime ≤ R.verifyTime then CulinaryLevel.trivial
  else if R.cookTime ≤ 2 * R.verifyTime then CulinaryLevel.easy
  else if R.cookTime ≤ 4 * R.verifyTime then CulinaryLevel.moderate
  else CulinaryLevel.hard

/-- Numeric level for ordering the hierarchy. -/
def CulinaryLevel.toNat : CulinaryLevel → ℕ
  | .trivial => 0
  | .easy => 1
  | .moderate => 2
  | .hard => 3
  | .impossible => 4

/-- The hierarchy is totally ordered. -/
instance : LE CulinaryLevel where
  le a b := a.toNat ≤ b.toNat

instance : DecidableRel (α := CulinaryLevel) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

/-! ## Main Theorems -/

/-
**Theorem 1: Kitchen-P ⊆ Kitchen-NP** (cooking implies verifiability).
    If a recipe can be cooked within a bound, and its verification time
    doesn't exceed its cooking time, then it can be verified within the same bound.
    This is the kitchen analogue of P ⊆ NP.
-/

/-
**Theorem 2: Sequential Composition Monotonicity**.
    The verification gap of a sequential composition is bounded by the
    component gaps. Specifically, if both recipes are hard, the composition is hard.
-/

/-
**Theorem 3: Parallel Composition Gap Bound**.
    Parallel composition cannot make a recipe "easier" — if either component
    is hard, the parallel composition has a specific gap structure.
-/

/-
**Theorem 4: Kitchen Reduction Transitivity**.
    Kitchen reductions compose: if R₁ reduces to R₂ and R₂ reduces to R₃,
    then R₁ reduces to R₃ with combined overhead.
-/

/-
**Theorem 5: Hierarchy Separation**.
    There exist recipes at each level of the culinary hierarchy.
    Specifically, we construct a recipe at level `hard`.
-/

/-
**Theorem 6: Destructive Verification Composition**.
    If either component has destructive verification, the composition does too.
    This models that "destructiveness propagates through recipe pipelines."
-/

/-
**Theorem 7: The Verification Gap Additivity Bound**.
    For sequential composition, the total cook time equals the sum of cook times,
    and similarly for verify times. This gives us control over the composite gap.
-/

/-
**Theorem 8: Quick Recipes are Closed Under Sequential Composition**.
    If both recipes are quick (C = V), their sequential composition is also quick.
    This means the class of "P = NP in kitchen" recipes forms a submonoid.
-/

/-
**Theorem 9: Hierarchy Level Monotonicity (for hard recipes)**.
    For recipes where cookTime > verifyTime (hard recipes), scaling up cook time
    preserves or increases the culinary level.
-/

/-! ## Concrete Examples -/

/-- A salad: 3 ingredients, 3 operations, cook time 3, verify time 3 (quick). -/
def salad : Recipe where
  numIngredients := 3
  numOperations := 3
  cookTime := 3
  verifyTime := 3
  destructive := false
  cook_pos := by omega
  verify_pos := by omega

/-- A soufflé: 5 ingredients, 8 operations, cook time 60, verify time 5 (hard + destructive). -/
def souffle : Recipe where
  numIngredients := 5
  numOperations := 8
  cookTime := 60
  verifyTime := 5
  destructive := true
  cook_pos := by omega
  verify_pos := by omega

/-- A bread: 4 ingredients, 6 operations, cook time 120, verify time 10 (hard). -/
def bread : Recipe where
  numIngredients := 4
  numOperations := 6
  cookTime := 120
  verifyTime := 10
  destructive := false
  cook_pos := by omega
  verify_pos := by omega

/-
Salad is a quick recipe.
-/

/-
Soufflé is a hard recipe.
-/

/-
Soufflé is classified as hard in the culinary hierarchy.
-/

/-
Salad is classified as impossible (since cookTime = verifyTime, the first branch catches it).
-/

/-
The soufflé-then-bread pipeline is also hard.
-/

/-! ## The Culinary Complexity Monoid

We show that recipes under sequential composition form a structure
with algebraic properties, making Kitchen Complexity Theory a
genuine algebraic-combinatorial framework. -/

/-
**Theorem 10: Verification Gap Weighted Average Bound**.
    For sequential composition, the composite verification gap is a weighted average
    of the component gaps (weighted by verify times). Formally:
    C(R₁∘R₂) / V(R₁∘R₂) is between min and max of {C(R₁)/V(R₁), C(R₂)/V(R₂)}.
    We prove the lower bound direction.
-/

/-
**Conjecture (Testable)**: For any recipe with cookTime > 4 * verifyTime and
    numOperations > numIngredients, the recipe is classified as `hard`.
    This is testable by constructing examples computationally.
-/


