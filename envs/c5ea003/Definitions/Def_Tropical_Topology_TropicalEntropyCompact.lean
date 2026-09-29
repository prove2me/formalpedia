-- Prove2me | Definitions.Def_Tropical_Topology_TropicalEntropyCompact
-- name    : Tropical_Topology_TropicalEntropyCompact
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:33:02.006961+00:00
-- url     : https://prove2.me/theorems/db173044-e19d-4fe3-b405-c2880cc90046
-- title:
--   Aether Catalog definitions — Tropical_Topology_TropicalEntropyCompact
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.Topology.TropicalEntropyCompact`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/Topology/TropicalEntropyCompact.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


/-!
# Compact Tropical Entropy: From Finite Minima to Topological Infima

This file develops the theory of tropical partition functions and entropy on compact
topological spaces, generalizing the finite tropical entropy formalism by replacing
`Finset.inf'` with order-theoretic `sInf`.

## Main definitions

* `tropicalPartitionCompact X E`: The tropical partition function on a compact space `X`
  with energy function `E : X → ℝ`, defined as `sInf (Set.range E)`.

## Main results

* `tropicalPartitionCompact_attained`: On a nonempty compact space, a lower semicontinuous
  energy function attains its minimum, which equals the tropical partition function.
* `tropicalPartitionCompact_le`: The tropical partition function is a lower bound for all
  energy values (for lsc energy functions).
* `le_tropicalPartitionCompact_of_forall_le`: Any universal lower bound on energies is
  at most the tropical partition function.
* `tropicalPartitionCompact_add_const`: Translation invariance of the tropical partition
  function under constant energy shifts.
* `tropicalPartitionCompact_mono`: Monotonicity under pointwise energy comparison.
* `tropicalPartitionCompact_pullback_surjective`: Invariance under surjective pullback
  (duplication invariance).
* `tropical_data_processing`: Data processing inequality — coarse-graining cannot decrease
  the minimum achievable energy.

## Mathematical significance

This establishes that tropical free energy is a topological invariant, not a finite-set
artifact. It opens connections between tropical geometry, idempotent analysis, compact
optimization, and information theory at zero temperature.

## Note on hypotheses

Several theorems require `LowerSemicontinuous E` to ensure `BddBelow (Set.range E)`,
which is necessary for `sInf` over `ℝ` (a conditionally complete lattice) to behave
correctly. Without boundedness, `sInf` on `ℝ` does not satisfy the expected properties.
The user-facing specification omitted this hypothesis in some places; we include it
where mathematically necessary.
-/

open Set Function Filter Topology

noncomputable section

/-- The tropical partition function on a compact topological space `X` with energy
function `E : X → ℝ`. This is the infimum of all energy values, which by
compactness and lower semicontinuity is actually attained. -/
def tropicalPartitionCompact
    (X : Type*) [TopologicalSpace X] [CompactSpace X]
    (E : X → ℝ) : ℝ :=
  sInf (Set.range E)

/-! ### Helper lemmas -/



/-
On a nonempty compact space, a lower semicontinuous function attains its
global minimum. This is the topological extreme value theorem for lsc functions.
-/

/-! ### Core API for the tropical partition function -/

/-
The tropical partition function is a lower bound for any energy value,
provided the energy function is lower semicontinuous (ensuring boundedness below).
-/

/-
Any value that is at most every energy value is at most the tropical
partition function.
-/

/-
On a nonempty compact space, a lower semicontinuous energy function attains
its minimum, which equals the tropical partition function. This is the
foundational attainment theorem.
-/

/-
The tropical partition function satisfies a universal characterization:
it is at most `a` if and only if some state has energy at most `a`.
-/

/-! ### Structural theorems -/

/-
Translation invariance: shifting all energies by a constant shifts the
tropical partition function by the same constant. This says tropical entropy
depends only on relative energy.
-/

/-
Left-addition version of translation invariance.
-/

/-
Monotonicity: if every state has at most as much energy under `E` as under `F`,
then the tropical partition function of `E` is at most that of `F`.
Requires lower semicontinuity of `E` to ensure the infimum is well-behaved.
-/

/-
Surjective pullback invariance: pulling back an energy function along a
surjection does not change the tropical partition function. This is the
topological analogue of idempotent duplication invariance.
-/

/-! ### Data processing inequality -/

/-
The tropical data processing inequality: if the observed energy `F` at `f(x)` is
always at most the latent energy `E` at `x`, then the tropical partition function of
the observed system is at most that of the latent system. Coarse-graining cannot
increase the minimum achievable energy.
-/

end


