-- Prove2me | solution 1 for TropicalEventGraph.tropMaxPlus_assoc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:56:38.154987+00:00
-- url     : https://prove2.me/submissions/4ada1cbe-f6e3-4798-974e-4050867c2386

-- Sol generated from Tropical/NeuralCoding/EventGraphSemantics.lean
import Mathlib
import Definitions.Def_Tropical_NeuralCoding_EventGraphSemantics
/-
# Compositional Tropical Semantics for Event Graphs

This file formalizes a compositional theory of timed event-graph systems
using max-plus (tropical) matrix algebra. The key results are:

1. **Series composition** of event graphs corresponds to tropical matrix
   multiplication (max-plus matrix product).
2. **Parallel composition** with disjoint interfaces corresponds to tropical
   block-diagonal matrix sum.
3. **Parallel composition** with shared interfaces corresponds to pointwise
   tropical maximum.
4. **Throughput/cycle-time bounds** compose modularly: series adds bounds,
   parallel takes the max.

## Mathematical Framework

We work with event graphs whose transfer semantics are captured by matrices
over `ℝ`. The tropical semiring operations are:
- Tropical addition: `max`
- Tropical multiplication: `+` (classical addition)

The transfer matrix `M(G)_{i,k}` of an event graph `G` with input interface `ι`
and output interface `κ` records the maximum-weight path from each input to
each output, representing the longest delay / critical path timing.

## Key Definitions

- `tropMaxPlus A B`: max-plus matrix multiplication
- `EventGraph ι κ`: event graph with typed interfaces
- `transfer G`: the transfer matrix of `G`
- `series G₁ G₂`: series composition
- `parallel G₁ G₂`: parallel (disjoint) composition
- `parallelShared G₁ G₂`: parallel (shared-interface) composition
- `CycleTimeBound G c`: predicate asserting cycle-time ≤ c
-/

open Matrix Finset

noncomputable section

open TropicalEventGraph

/-! ## Max-Plus Matrix Operations -/




/-! ## Event Graph Structure -/


/-! ## Transfer Semantics -/


/-! ## Composition Operations -/




/-! ## Theorem 1: Series Composition = Tropical Matrix Multiplication -/


/-! ## Theorem 2a: Parallel (Disjoint) = Block Diagonal -/


/-! ## Theorem 2b: Parallel (Shared) = Pointwise Max -/


/-! ## Cycle-Time Bounds -/


/-! ## Theorem 3a: Series Throughput Certification -/

/-
**Series throughput theorem**: If `G₁` has cycle-time bound `c₁` and
    `G₂` has cycle-time bound `c₂`, then their series composition has
    cycle-time bound `c₁ + c₂`.
-/

/-! ## Theorem 3b: Parallel (Disjoint) Throughput Certification -/

/-
**Parallel throughput theorem (disjoint)**: Cycle-time bound is max.
    Requires `0 ≤ c₁` and `0 ≤ c₂` because off-diagonal (cross-system)
    entries are `0`, representing the absence of paths.
-/

/-! ## Theorem 3c: Shared-Parallel Throughput Certification -/

/-
**Shared-parallel throughput theorem**: Cycle-time bound is max.
-/

/-! ## Associativity of Max-Plus Matrix Multiplication -/

/-
Max-plus matrix multiplication is associative.
-/


/-! ## Commutativity and Associativity of Shared Parallel -/



/-! ## Concrete Examples -/

/-
A simple 2-stage pipeline: two scalar event graphs with delays 3 and 5.
    Series composition yields delay 8 = 3 + 5 (tropical multiplication).
-/
example : ∀ (i k : Fin 1), transfer (series
    (⟨fun (_ : Fin 1) (_ : Fin 1) => (3 : ℝ)⟩ : EventGraph (Fin 1) (Fin 1))
    (⟨fun (_ : Fin 1) (_ : Fin 1) => (5 : ℝ)⟩ : EventGraph (Fin 1) (Fin 1))) i k
    = (8 : ℝ) := by
  intro i k; fin_cases i; fin_cases k; norm_num [ transfer, series, tropMaxPlus ] ;

/-
Fork-join: two parallel paths with delays 3 and 5.
    Shared parallel composition yields delay 5 = max(3, 5).
-/
example : ∀ (i k : Fin 1), transfer (parallelShared
    (⟨fun (_ : Fin 1) (_ : Fin 1) => (3 : ℝ)⟩ : EventGraph (Fin 1) (Fin 1))
    (⟨fun (_ : Fin 1) (_ : Fin 1) => (5 : ℝ)⟩ : EventGraph (Fin 1) (Fin 1))) i k
    = (5 : ℝ) := by
  norm_num [ Fin.eq_zero, transfer, parallelShared, tropPointwiseMax ]

/-- A 2×2 pipeline network: two 2-input/2-output stages composed in series.
    Demonstrates that max-plus matrix multiplication computes critical paths
    through a multi-port pipeline. -/
example : let G₁ : EventGraph (Fin 2) (Fin 2) :=
    ⟨!![1, 3; 2, 4]⟩
  let G₂ : EventGraph (Fin 2) (Fin 2) :=
    ⟨!![5, 6; 7, 8]⟩
  ∀ i k, transfer (series G₁ G₂) i k =
    tropMaxPlus (transfer G₁) (transfer G₂) i k := by
  intro G₁ G₂ i k
  rfl


open TropicalEventGraph in
theorem solution    {ι κ μ ν : Type} [Fintype κ] [Fintype μ]
    [DecidableEq κ] [DecidableEq μ]
    [Nonempty κ] [Nonempty μ]
    (A : Matrix ι κ ℝ) (B : Matrix κ μ ℝ) (C : Matrix μ ν ℝ) :
    tropMaxPlus (tropMaxPlus A B) C = tropMaxPlus A (tropMaxPlus B C) := by
  -- By definition of tropMaxPlus, we know that for any i and k, the entry of the resulting matrix at (i, k) is the supremum over μ of (supremum over κ of (A i κ + B κ μ)) + C μ k.
  ext i k; simp [tropMaxPlus];
  refine' le_antisymm ( Finset.sup'_le _ _ _ ) ( Finset.sup'_le _ _ _ );
  · intro b hb;
    obtain ⟨ j, hj ⟩ := Finset.exists_mem_eq_sup' ( Finset.univ_nonempty ) ( fun j => A i j + B j b );
    refine' le_trans _ ( Finset.le_sup' _ ( Finset.mem_univ j ) );
    linarith [ Finset.le_sup' ( fun j_1 => B j j_1 + C j_1 k ) hb ];
  · intro b hb;
    obtain ⟨ c, hc ⟩ := Finset.exists_mem_eq_sup' ( Finset.univ_nonempty ) ( fun j => B b j + C j k );
    refine' le_trans _ ( Finset.le_sup' _ ( Finset.mem_univ c ) );
    linarith [ show A i b ≤ Finset.univ.sup' ( Finset.univ_nonempty ) ( fun j => A i j + B j c ) - B b c from by linarith [ Finset.le_sup' ( fun j => A i j + B j c ) ( Finset.mem_univ b ) ] ]
