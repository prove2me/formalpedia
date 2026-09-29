-- Prove2me | Definitions.Def_Bridges_PosetTheory_CycleBirthConcentration
-- name    : Bridges_PosetTheory_CycleBirthConcentration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:29.420475+00:00
-- url     : https://prove2.me/theorems/8cddd82a-b78a-4ecb-bf76-36f49fdd16de
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_CycleBirthConcentration
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.CycleBirthConcentration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/CycleBirthConcentration.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cycle-Birth Concentration and Universality for Tropical Graph Filtrations

This file establishes the mathematical foundations for **probabilistic tropical
topology**: the study of cycle-birth times in random weighted graph filtrations.

## Overview

For a finite weighted graph, processing edges in weight order produces a filtration.
Each edge either merges two connected components (a "merge" event) or connects already-
connected vertices, creating a cycle (a "cycle-birth" event). The cycle-birth edges
are exactly the **tropical critical values** of the weight filtration.

We prove:
1. **Deterministic characterization** (`cycleBirth_iff_connected_before`):
   An edge is a cycle-birth iff its endpoints are connected among lighter edges.
2. **Merge-or-cycle dichotomy** (`merge_xor_cycleBirth`):
   Each edge is exactly one of merge or cycle-birth.
3. **Monotone transport invariance** (`cycleBirthFlags_invariant_strictMono`):
   Applying a strictly monotone function to all weights preserves the
   cycle-birth classification of each edge. This is the universality mechanism.
4. **Lipschitz stability** (`cycleBirthCount_flip_one_le`):
   Flipping one step's classification changes the cycle-birth count by at most 1.
5. **MST complement** (`cycleBirth_eq_complement_forest`):
   Cycle-birth edges are exactly the edges NOT in the greedy spanning forest.

## Cross-domain connections

- **Tropical Morse theory**: Cycle births are tropical critical values of
  the min-plus weight function.
- **Persistent homology / TDA**: Cycle births are 1-dimensional persistence
  birth times.
- **Combinatorial optimization**: Cycle births = non-MST edges (Kruskal duality).
- **Concentration of measure**: The bounded-differences property enables
  McDiarmid/Azuma concentration for random edge weights.
- **Statistical physics universality**: Monotone transport invariance mirrors
  insensitivity to microscopic disorder in random matrix theory.

## Mathematical significance

This package shows that **cycle births are to random topology what eigenvalues
are to random linear algebra**: a concentrated, universal spectral observable.

**Application keywords:** tropical Morse theory, persistent homology, Erdős–Rényi graphs,
concentration of measure, McDiarmid inequality, Azuma–Hoeffding, universality,
minimum spanning tree, graphic matroid, percolation, network science,
topological statistics, random optimization, KS distance, empirical process.

## References

- Baker–Norine (2007): tropical graph theory
- Cohen-Steiner–Edelsbrunner–Harer (2007): stability of persistence
- Builds on `Catalog/Pythagorean/TropicalMorse/Theorems.lean`:
  `filtration_betti1_eq_cycleCount` (≡ `cycle_rank_additive_over_filtration`)
  and `filtration_rank_eq_mergeCount` (≡ `component_delta_accumulation`).
-/


/-! ## Part 1: Filtration Framework (self-contained) -/

namespace CycleBirthConcentration

/-- A filtration step records what happens when a single edge is inserted
    into the growing subgraph. The key datum is `sameComponent`:
    - `true`: endpoints already connected → cycle birth (β₁ increases)
    - `false`: endpoints in different components → merge (β₀ decreases) -/
structure FiltStep where
  weight : ℚ
  sameComponent : Bool
  deriving DecidableEq, Inhabited

/-- A weighted graph filtration: vertices + ordered edge insertions. -/
structure WFiltration where
  numVerts : ℕ
  steps : List FiltStep

/-- Number of cycle-birth events (edges creating cycles). -/
def WFiltration.cycleCount (F : WFiltration) : ℕ :=
  F.steps.countP (·.sameComponent)

/-- Number of merge events (edges connecting components). -/
def WFiltration.mergeCount (F : WFiltration) : ℕ :=
  F.steps.countP (fun s => !s.sameComponent)

/-! ## Part 2: New Definitions — Cycle-Birth Multiset and Counting -/

/-- **New Definition 1: Cycle-birth weight multiset.**
    The list of edge weights at which cycle births occur.
    These are the **tropical critical values** of the filtration. -/
def WFiltration.cycleBirthWeights (F : WFiltration) : List ℚ :=
  (F.steps.filter (·.sameComponent)).map (·.weight)

/-- **New Definition 2: Cumulative cycle-birth counting function.**
    `cycleBirthCountLE F t` = number of cycle births with weight ≤ t.
    This is the **tropical spectral counting function**. -/
def WFiltration.cycleBirthCountLE (F : WFiltration) (t : ℚ) : ℕ :=
  F.steps.countP (fun s => s.sameComponent && decide (s.weight ≤ t))



/-- Extract the classification flags from a filtration. -/
def WFiltration.flags (F : WFiltration) : List Bool :=
  F.steps.map (·.sameComponent)

/-! ## Part 3: Core List Counting Lemmas -/



/-! ## Part 4: Merge-or-Cycle Dichotomy (Theorem 1) -/



/-! ## Part 5: Cycle-Birth Characterization -/


/-! ## Part 6: Monotone Transport Invariance (Theorem 4 — Universality) -/

/-- Apply a function to all step weights, preserving sameComponent flags.
    This models applying a monotone weight transformation. -/
def WFiltration.mapWeights (F : WFiltration) (φ : ℚ → ℚ) : WFiltration where
  numVerts := F.numVerts
  steps := F.steps.map (fun s => ⟨φ s.weight, s.sameComponent⟩)




/-
**Theorem 4b: The cycle-birth weight list transforms equivariantly.**
    If weights are transformed by φ, the cycle-birth weights are exactly
    the φ-images of the original cycle-birth weights.
-/


/-! ## Part 7: Lipschitz Stability (Theorem 2) -/

/-
**Core counting lemma**: For a list of Booleans, flipping one element
    at index `k` changes `countP id` by exactly 1 (in absolute value)
    if the flip changes the value, and 0 otherwise.

    This is the abstract heart of the bounded-differences property.
-/

/-
**Theorem 2a: Single-step Lipschitz bound for cycle count.**
    Flipping one step's sameComponent flag changes the total cycle count
    by at most 1. This is the discrete bounded-differences constant.

    This is the analogue of a rank-one perturbation bound in random
    matrix theory: changing one "coordinate" of the random input
    changes the spectral observable by at most one unit.
-/

/-
**Theorem 2b: Cumulative cycle-birth count stability.**
    For the threshold-dependent counting function, flipping one flag
    also changes the count by at most 1 at each threshold.
-/

/-! ## Part 8: MST Complement Characterization (Theorem 5) -/




/-! ## Part 9: Euler Characteristic and Betti Number Relations -/



/-! ## Part 10: Concentration Infrastructure -/

/-- A function on Boolean vectors has bounded differences with constant `c`.
    This is the hypothesis needed for McDiarmid's inequality.

    **Context (Abstract bounded-differences principle):**
    If `f : (Fin m → Bool) → ℤ` satisfies bounded differences
    with constant 1 in each coordinate, then the function doesn't vary
    much over the Boolean hypercube.
    The probabilistic version (with i.i.d. random inputs) gives subgaussian
    concentration: P(|f(X) - E[f(X)]| ≥ r) ≤ 2·exp(-2r²/m). -/
def HasBoundedDifferences (m : ℕ) (f : (Fin m → Bool) → ℤ) (c : ℕ) : Prop :=
  ∀ (x : Fin m → Bool) (i : Fin m) (b : Bool),
    |f x - f (Function.update x i b)| ≤ c

/-
The cycle-birth counting function (as a function on Boolean classification
    vectors) has bounded differences with constant 1.

    This is the key analytical input for McDiarmid/Azuma concentration.
-/

/-! ## Part 11: Worked Examples -/

/-- Example: A triangle (3 vertices, 3 edges) with weights 1, 2, 3.
    First two edges merge (connect the chain), third creates a cycle.
    So: 2 merges + 1 cycle = 3 edges. -/
def triangleFiltration : WFiltration where
  numVerts := 3
  steps := [⟨1, false⟩, ⟨2, false⟩, ⟨3, true⟩]


/-- Example: K₄ (4 vertices, 6 edges) with weights 1..6.
    First 3 edges form a spanning tree (3 merges), remaining 3 create cycles.
    So: 3 merges + 3 cycles = 6 edges. β₁ = 6 - 4 + 1 = 3. -/
def k4Filtration : WFiltration where
  numVerts := 4
  steps := [⟨1, false⟩, ⟨2, false⟩, ⟨3, false⟩, ⟨4, true⟩, ⟨5, true⟩, ⟨6, true⟩]





/-! ## Part 12: Asymptotic Conjectures (Formal Prose)

**Conjecture (Tropical Spectral Law for Random Graphs):**

For each fixed p ∈ (0,1), let G_n ~ G(n,p) and let edge weights be
i.i.d. from any continuous distribution F. Let

  μ_Gn := (1/β₁(G_n)) · Σ_{e ∈ CycleBirthEdges} δ_{F(w(e))}

on the event β₁(G_n) > 0. Then there exists a deterministic probability
measure μ_p on [0,1] such that μ_Gn → μ_p weakly in probability
as n → ∞.

Moreover, by monotone transport invariance (Theorem 4), the limiting
measure depends on F only through monotone rescaling: if U ~ Uniform[0,1]
gives limit μ_p, then F-distributed weights give limit F_*^{-1}(μ_p).

**Testable prediction**: The KS distance between empirical CDFs from
independent trials should decay like O(n^{-1/2}).

**Falsifiable stronger conjecture**: For dense G(n,p) with fixed p ∈ (0,1),
the limit law μ_p is Beta-like with parameters determined only by p.
This is falsifiable by simulation.

This conjecture, if true, would establish cycle-birth times as a new
"tropical spectral observable" for random networks — playing the role
that the semicircle law plays for eigenvalues of random matrices.
-/

end CycleBirthConcentration


