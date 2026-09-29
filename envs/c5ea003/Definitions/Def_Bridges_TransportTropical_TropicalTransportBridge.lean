-- Prove2me | Definitions.Def_Bridges_TransportTropical_TropicalTransportBridge
-- name    : Bridges_TransportTropical_TropicalTransportBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:07.110228+00:00
-- url     : https://prove2.me/theorems/c097c617-189a-4d0f-9746-87ab5ca7933b
-- title:
--   Aether Catalog definitions — Bridges_TransportTropical_TropicalTransportBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TransportTropical.TropicalTransportBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TransportTropical/TropicalTransportBridge.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical-Transport Bridge: Unifying Min-Plus Algebra with Optimal Transport

This file establishes deep connections between tropical (min-plus) matrix algebra
and discrete optimal transport theory, showing that both are governed by the same
optimization principles.

## Main results

- `tropMul_eq_min_transport_cost`: The tropical matrix product at (i,j) equals the
    minimum over intermediate points of the sum of costs, which is exactly the
    structure of shortest-path/transport optimization.

- `tropMul_mono`: Tropical multiplication is monotone with respect to the
    entrywise partial order on matrices.

- `tropMul_triangle`: Tropical matrix multiplication satisfies a triangle-like
    inequality relating diagonal entries.

- `tropPow_diag_le_trace_bound`: Diagonal entries of tropical powers are bounded
    by the minimum diagonal entry scaled appropriately.

- `permCost_ge_tropMul_diag`: The assignment cost of any permutation is bounded
    below by the tropical product diagonal, connecting combinatorial optimization
    with tropical spectral theory.

These results demonstrate that transport minimization and tropical minimization
are manifestations of one formal optimization language.
-/

open Finset BigOperators

variable {n : ℕ}

/-- Min-plus (tropical) matrix multiplication. -/
noncomputable def tropMulB (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ⨅ k : Fin n, (A i k + B k j)

/-! ## Monotonicity of tropical multiplication -/

/-
Tropical multiplication is monotone: if A ≤ A' and B ≤ B' entrywise,
    then A ⊗ B ≤ A' ⊗ B' entrywise.
-/

/-! ## Connection to assignment/permutation costs -/


/-
The tropical product diagonal entry is at most the sum of corresponding
    entries along any path through an intermediate vertex.
-/

/-
The assignment cost of any permutation bounds the sum of tropical diagonal entries.
    This is because each diagonal entry tropMul(A,B)(i,i) ≤ A(i,σ(i)) + B(σ(i),i)
    for any σ, and summing over i gives the bound.
-/

/-
When A = B = c (same cost matrix), the tropical square's diagonal entry
    at i gives the minimum 2-step round-trip cost through i.
-/

/-! ## Tropical powers and shortest paths -/

/-- Tropical power (0-indexed, matching MinPlus.lean convention). -/
noncomputable def tropPowB (A : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => A
  | m + 1 => tropMulB (tropPowB A m) A

/-
The diagonal of the tropical square is at most twice the diagonal of the original.
-/

/-! ## Wasserstein-tropical connection -/

/-- Transport cost definition (local copy for self-containment). -/
def transportCostB (c : Fin n → Fin n → ℝ) (π : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, π i j * c i j


/-- Pushforward by equivalence (local copy). -/
def pushforwardEquivB (e : Fin n ≃ Fin n) (μ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => μ (e.symm i)

/-
The Wasserstein distance for nonneg cost functions is nonneg when plans exist.
-/

/-
Pushforward preserves the probability vector property.
-/

/-
The identity equivalence acts trivially on pushforward.
-/

/-
Composing pushforwards corresponds to composing equivalences.
-/


