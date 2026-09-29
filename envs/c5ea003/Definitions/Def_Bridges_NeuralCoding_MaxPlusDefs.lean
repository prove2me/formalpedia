-- Prove2me | Definitions.Def_Bridges_NeuralCoding_MaxPlusDefs
-- name    : Bridges_NeuralCoding_MaxPlusDefs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:27.93773+00:00
-- url     : https://prove2.me/theorems/baaa65f2-78f9-4c2c-8c66-4436a6fa1a11
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_MaxPlusDefs
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.MaxPlusDefs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/MaxPlusDefs.lean by skeleton subtraction
import Mathlib

/-!
# Max-Plus Algebra: Core Definitions

This file establishes the foundational definitions for finite-dimensional max-plus
(tropical) linear algebra over real-weighted matrices.

## Main definitions

* `maxPlusMul` - tropical matrix-vector multiplication
* `tropicalMatMul` - tropical matrix-matrix multiplication
* `tropicalMatPow` - iterated tropical matrix powers
* `walkWeight` - weight of a directed walk in the weighted complete digraph
* `cycleMean` - average weight per edge in a cycle
* `maxCycleMeanOfLength` - max cycle mean over cycles of a given length
* `maxCycleMean` - the maximal cycle mean (= tropical spectral radius)
* `maxEntry` - maximum entry of a matrix

## Overview

We work with `Fin n → Fin n → ℝ` matrices representing the weight function of a
complete weighted digraph on `n` vertices. In this model every edge is present
(with possibly negative weight), so every matrix is trivially strongly connected.
The "irreducibility" condition is therefore automatic over `ℝ` and becomes
non-trivial only when one moves to `WithBot ℝ` (where `-∞` means "no edge").
-/

noncomputable section

open Finset BigOperators

variable {n : ℕ}

/-! ### Max-plus matrix operations -/

/-- Max-plus matrix-vector multiplication: `(M ⊗ x)_i = max_j (M_i_j + x_j)`. -/
def maxPlusMul (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (hn : 0 < n) :
    Fin n → ℝ :=
  fun i => Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => M i j + x j)

/-- Tropical matrix-matrix multiplication: `(A ⊗ B)_ij = max_k (A_ik + B_kj)`. -/
def tropicalMatMul (hn : 0 < n) (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun k => A i k + B k j)


/-- Tropical matrix power by repeated multiplication. -/
def tropicalMatPow (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) :
    ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => fun _i _j => 0
  | k + 1 => tropicalMatMul hn M (tropicalMatPow hn M k)

/-- Maximum entry of a matrix over `Fin n × Fin n`. -/
def maxEntry (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun i => Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => M i j))

/-! ### Directed walks and cycles -/

/-- Weight of a directed walk given as a list of vertices.
    For `[v₀, v₁, ..., vₖ]`, the weight is `M v₀ v₁ + M v₁ v₂ + ... + M vₖ₋₁ vₖ`. -/
def walkWeight (M : Matrix (Fin n) (Fin n) ℝ) : List (Fin n) → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => M a b + walkWeight M (b :: rest)




/-! ### Maximal cycle mean -/



/-! ### Computable max cycle mean via enumeration

For a concrete algorithm, we enumerate all cycles up to length n+1 and
compute the maximum cycle mean. This avoids the `sSup` abstraction.
-/






/-! ### Irreducibility -/


/-! ### Spectral radius via asymptotic growth -/


end


