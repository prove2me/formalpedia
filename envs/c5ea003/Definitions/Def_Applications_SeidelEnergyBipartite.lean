-- Prove2me | Definitions.Def_Applications_SeidelEnergyBipartite
-- name    : Applications_SeidelEnergyBipartite
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:43.524263+00:00
-- url     : https://prove2.me/theorems/6ef3be64-f6aa-4d17-b7b2-2b8e30e76ad1
-- title:
--   Aether Catalog definitions — Applications_SeidelEnergyBipartite
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.SeidelEnergyBipartite`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/SeidelEnergyBipartite.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Seidel energy of complete bipartite graphs — a spectral/combinatorial bridge

The **Seidel matrix** of a graph `G` on vertex set `V` is the symmetric matrix
`S` with `S i i = 0`, `S i j = -1` when `i ~ j` and `S i j = +1` when `i ≠ j` and
`¬ i ~ j`.  Equivalently `S = J - I - 2A` where `A` is the adjacency matrix and `J`
the all-ones matrix.  The **Seidel energy** of `G` is `∑ |λ|` over the eigenvalues
`λ` of `S`.

For the complete bipartite graph `K_{m,n}` the vertex set is `Fin m ⊕ Fin n`, and
two distinct vertices are adjacent exactly when they lie in different parts.  Hence
the Seidel matrix has entry `+1` inside a part and `-1` across parts, i.e.

  `S i j = w i * w j - δ i j`,   where `w = (+1 on the left, -1 on the right)`.

This is the rank-one structure `S = w wᵀ - I` (a `vecMulVec` minus the identity).
This file exploits that structure to compute the entire Seidel spectrum and the
Seidel energy in closed form:

* `Sd_charpoly_factored` : the characteristic polynomial factors as
  `(X + 1)^{m+n-1} (X - (m+n-1))`, so the Seidel spectrum of `K_{m,n}` is
  `{ m+n-1 }` together with `-1` of multiplicity `m+n-1`;
* `seidelEnergy_Kmn` : **the Seidel energy of `K_{m,n}` equals `2(m+n-1)`**.

The bridge `energy_eq_roots` connects the analytic definition of energy (a sum of
absolute values of the `IsHermitian` eigenvalues) with the algebraic object
`charpoly.roots`, which is what makes the rank-one determinant computation usable.
-/

open Matrix Polynomial
open scoped BigOperators

noncomputable section

namespace SeidelBipartite

/-- The ±1 weight vector cutting `Fin m ⊕ Fin n` into its two parts:
`+1` on the left part, `-1` on the right part. -/
def wt (m n : ℕ) : (Fin m ⊕ Fin n) → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

/-- The **Seidel matrix** of the complete bipartite graph `K_{m,n}`, written in its
rank-one form `w wᵀ - I`. Its `(i,j)` entry is `+1` inside a part, `-1` across
parts, and `0` on the diagonal. -/
def Sd (m n : ℕ) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  vecMulVec (wt m n) (wt m n) - 1

/-- The **Seidel energy** of a real symmetric matrix: the sum of the absolute
values of its (real) eigenvalues. -/
def seidelEnergy {V : Type*} [Fintype V] [DecidableEq V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) : ℝ := ∑ i, |hA.eigenvalues i|







end SeidelBipartite


