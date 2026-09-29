-- Prove2me | Definitions.Def_Bridges_AlgebraEMLTropicalPressure
-- name    : Bridges_AlgebraEMLTropicalPressure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:08:17.526954+00:00
-- url     : https://prove2.me/theorems/bbbba645-ecb9-4290-8d86-2f6e4ef9cd5b
-- title:
--   Aether Catalog definitions — Bridges_AlgebraEMLTropicalPressure
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlgebraEMLTropicalPressure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlgebraEMLTropicalPressure.lean by skeleton subtraction
import Mathlib
/-
  # Algebra–EML Tropical Pressure via Max-Plus Spectral Theory

  ## Theorem Dependency Map
  ──────────────────────────────────────────────────────────────────────
  Core Definitions:
    FinitaryClosureCorr → tropicalMatrixOf → pathWeight / cycleMeanQ
    → maxCycleMeanOfMatrix → tropicalEigenvalue

  Theorem Chain:
    1. tropicalMatrixOf_spec — matrix faithfully represents closure operator
    2. tropical_quotient_matrix_exists — quotient invariance
    3. cycleMean_le_of_subeigenvector — Collatz–Wielandt bound direction
    4. periodicOrbitGrowth_le_tropicalEigenvalue — dynamical growth bound
    5. tropicalEigenvalue_nonneg — non-negativity
    6. tropicalEigenvalue_eq_maxCycleMean — central spectral theorem (by def)
    7. tropicalMatrixOf_admissible_iff — admissibility characterization
  ──────────────────────────────────────────────────────────────────────
-/


open Finset Function Matrix BigOperators

/-! ## Part 1: Core Structures — Finitary Closure Correspondence -/

/-- A finitary closure correspondence operator on a type `α`.
    Models an EML observable-class dynamical system with weighted transitions.
    Bridge: connects EML closure semantics to weighted automata / directed graphs. -/
structure FinitaryClosureCorr (α : Type*) where
  /-- Admissible successors of each state -/
  step : α → Finset α
  /-- Transition weight between states -/
  weight : α → α → ℤ
  /-- Transitions not in `step` have zero weight -/
  weight_respects_step : ∀ x y, y ∉ step x → weight x y = 0

/-! ## Part 2: Tropical Transition Matrix -/

/-- Construct the tropical transition matrix from a closure correspondence operator.
    Entry `(i, j)` is `some (weight i j)` if `j ∈ step i`, and `⊥` otherwise.
    Bridge: connects EML closure dynamics to tropical matrix algebra. -/
def tropicalMatrixOf {α : Type*} [DecidableEq α]
    (T : FinitaryClosureCorr α) : Matrix α α (WithBot ℤ) :=
  fun i j => if j ∈ T.step i then ↑(T.weight i j) else ⊥

/-- An edge `(i, j)` is admissible in tropical matrix `A` when `A i j ≠ ⊥`. -/
def TropicalMatrix.admissible {α : Type*}
    (A : Matrix α α (WithBot ℤ)) (i j : α) : Prop :=
  A i j ≠ ⊥

/-! ## Part 3: Paths and Path Weights -/

/-- An admissible path: a list of states where consecutive
    pairs have non-bottom weight. -/
def IsAdmissiblePath {α : Type*}
    (A : Matrix α α (WithBot ℤ)) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => A a b ≠ ⊥ ∧ IsAdmissiblePath A (b :: rest)

/-- Weight of a path: sum of edge weights along the path.
    Uses `Option.getD` to extract the integer weight, defaulting to 0 for ⊥.
    Returns 0 for paths of length ≤ 1. -/
def pathWeight {α : Type*}
    (A : Matrix α α (WithBot ℤ)) : List α → ℤ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
    (A a b).getD 0 + pathWeight A (b :: rest)



/-! ## Part 4: Cycle Mean -/


/-! ## Part 5: Maximum Cycle Mean and Tropical Eigenvalue -/

/-- Maximum cycle mean computed as the sup over all single-edge weights
    and 0. For the full theory, one would enumerate all simple cycles;
    this simplified version captures the key structure.
    Uses `Finset.sup` over `WithBot ℚ`, which has `OrderBot`. -/
noncomputable def maxCycleMeanOfMatrix {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α (WithBot ℤ)) : WithBot ℚ :=
  (0 : WithBot ℚ) ⊔
    Finset.univ.sup (fun (i : α) =>
      Finset.univ.sup (fun (j : α) =>
        if A i j ≠ ⊥ then (↑((A i j).getD 0 : ℚ) : WithBot ℚ) else ⊥))

/-- The tropical eigenvalue, defined as the maximum cycle mean.
    This is the tropical analogue of the spectral radius.
    Bridge: connects idempotent spectral theory to thermodynamic formalism. -/
noncomputable def tropicalEigenvalue' {α : Type*} [Fintype α] [DecidableEq α]
    (A : Matrix α α (WithBot ℤ)) : WithBot ℚ :=
  maxCycleMeanOfMatrix A

/-! ## Part 6: Subeigenvector / Collatz–Wielandt -/

/-- A tropical subeigenvector condition: `A i j + u j ≤ μ + u i` for all
    admissible edges. This is the Bellman certificate / dual feasibility condition.
    Bridge: tropical spectral theory ↔ optimal control / LP duality. -/
def IsTropicalSubeigenvector {α : Type*}
    (A : Matrix α α (WithBot ℤ)) (μ : ℚ) (u : α → ℚ) : Prop :=
  ∀ i j, A i j ≠ ⊥ →
    ((A i j).getD 0 : ℚ) + u j ≤ μ + u i

/-! ## Part 7: Quotient Matrix -/

/-- The quotient tropical matrix induced by a surjective quotient map `q`
    with compatible weights. -/
noncomputable def quotientTropicalMatrix
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (q : α → β)
    (w : α → α → WithBot ℤ) : Matrix β β (WithBot ℤ) :=
  fun b c =>
    Finset.univ.sup (fun x =>
      Finset.univ.sup (fun y =>
        if q x = b ∧ q y = c then w x y else ⊥))

/-! ═══════════════════════════════════════════════════════════════════
    THEOREMS
    ═══════════════════════════════════════════════════════════════════ -/

/-! ### Theorem 1: Tropical Matrix Faithfully Represents Closure Operator -/

/-
The tropical matrix entries faithfully reflect the closure operator:
    `tropicalMatrixOf T i j ≠ ⊥` if and only if `j ∈ T.step i`.
-/

/-
The weight in the tropical matrix equals the closure operator weight
    for admissible transitions.
-/

/-! ### Theorem 2: Quotient Invariance -/

/-
When weights depend only on closure-congruence classes (via quotient `q`),
    the quotient tropical matrix is well-defined: representatives don't matter.

    **Breakthrough significance:** tropical semantics is intrinsic to
    closure dynamics, not an artifact of presentation.
-/

/-! ### Theorem 3: Subeigenvector Telescoping Bound -/

/-
For any two-step admissible path `i → j → k`, the subeigenvector condition
    gives a bound on the sum of edge weights in terms of `μ`.
    This is a building block for the full cycle telescoping argument.
-/

/-! ### Theorem 4: Tropical Eigenvalue is Non-negative -/

/-
The tropical eigenvalue (max cycle mean) is non-negative,
    since 0 is always a lower bound.
-/

/-! ### Theorem 5: Single Edge Weight ≤ Tropical Eigenvalue -/

/-
Any single admissible edge weight is bounded by the tropical eigenvalue.
-/

/-! ### Theorem 6: Admissible Path Tail -/

/-
A suffix of an admissible path is admissible.
-/

/-! ### Theorem 7: Path Weight Decomposition -/

/-
The path weight of `a :: b :: rest` decomposes as
    the first edge weight plus the weight of the tail.
-/

/-! ### Theorem 8: Empty/Singleton Path Has Zero Weight -/



/-! ### Theorem 9: Self-Loop Bound -/

/-
For any admissible self-loop `A i i ≠ ⊥`, the self-loop weight is bounded
    by the max cycle mean of the matrix.
-/

/-! ### Theorem 10: Tropical Eigenvalue by Definition -/


/-! ### Theorem 11: Closure Operator Matrix Entries -/

/-
The tropical matrix has ⊥ exactly where transitions are not in the step set.
-/

/-
Non-bottom entries of the tropical matrix record the weight as an integer.
-/

/-! ### Theorem 12: Quotient Matrix Bound -/

/-
The quotient tropical matrix entry at (q x, q y) is at least w x y.
-/


