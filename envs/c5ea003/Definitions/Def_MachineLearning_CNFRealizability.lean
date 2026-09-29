-- Prove2me | Definitions.Def_MachineLearning_CNFRealizability
-- name    : MachineLearning_CNFRealizability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:37:54.483064+00:00
-- url     : https://prove2.me/theorems/f71010a7-fdb7-4566-83da-be8bfe55a7d8
-- title:
--   Aether Catalog definitions — MachineLearning_CNFRealizability
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CNFRealizability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CNFRealizability.lean by skeleton subtraction
import Mathlib

/-!
# Cantor Normal Form Realizability and ω^ω Realization

This module extends the ordinal collapse theory to prove that `InfBranchTree`
provides a **complete constructive semantics for all ordinals below ω^ω** via
Cantor normal form, and constructs a tree realizing `ω^ω` itself.

## Main Definitions

* `InfBranchTree.prepend` — Tree composition yielding ordinal addition on ranks.
* `InfBranchTree.mulByNat` — Tree repetition yielding ordinal multiplication by ℕ.
* `InfBranchTree.omegaPowTree` — Canonical tree of rank `ω^n`.
* `InfBranchTree.cnfTree` — Tree built from a CNF coefficient/exponent list.
* `InfBranchTree.omegaToOmegaTree` — Canonical tree of rank `ω^ω`.

## Main Results

### Cluster E: Tree Algebra Operations
* `rank_prepend` — `rank (prepend s t) = rank s + rank t`
* `rank_mulByNat` — `rank (mulByNat t k) = rank t * k`

### Cluster F: Ordinal Power Realization
* `rank_omegaPowTree` — `rank (omegaPowTree n) = ω^n`

### Cluster G: Cantor Normal Form Realizability
* `rank_cnfTree` — CNF lists are exactly realized by `cnfTree`.

### Cluster H: ω^ω Realization
* `rank_omegaToOmegaTree` — `rank omegaToOmegaTree = ω^ω`
-/

noncomputable section

open Ordinal

/-! ## InfBranchTree (reproduced from Basic) -/

/-- A well-founded tree with countably infinite branching at each internal node. -/
inductive InfBranchTree where
  | leaf : InfBranchTree
  | node : (ℕ → InfBranchTree) → InfBranchTree

namespace InfBranchTree

/-- The ordinal rank (depth) of an infinitely branching tree. -/
def rank : InfBranchTree → Ordinal
  | .leaf => 0
  | .node children => ⨆ i : ℕ, Order.succ (rank (children i))

/-! ## Cluster E: Tree Algebra Operations -/

/-- `prepend s t` inserts `s` at every leaf of `t`.
When `t = leaf`, the result is `s`. When `t = node f`, each child is recursively prepended.
This yields ordinal addition: `rank (prepend s t) = rank s + rank t`. -/
def prepend : InfBranchTree → InfBranchTree → InfBranchTree
  | s, .leaf => s
  | s, .node f => .node (fun i => prepend s (f i))




/-- `mulByNat t k` builds a tree of rank `rank t * k` by iterating prepend. -/
def mulByNat : InfBranchTree → ℕ → InfBranchTree
  | _, 0 => .leaf
  | t, k + 1 => prepend t (mulByNat t k)

/-
**Rank Multiplication Theorem**: `mulByNat` realizes ordinal multiplication by ℕ.
-/

/-! ## Cluster F: Ordinal Power Realization -/

/-- `omegaPowTree n` is the canonical tree of rank `ω^n`.
- `omegaPowTree 0 = node (fun _ => leaf)` has rank 1 = ω^0.
- `omegaPowTree (n+1) = node (fun k => mulByNat (omegaPowTree n) k)` has rank ω^(n+1)
  since `⨆ k, succ(ω^n * k) = ω^n * ω = ω^(n+1)`. -/
def omegaPowTree : ℕ → InfBranchTree
  | 0 => .node (fun _ => .leaf)
  | n + 1 => .node (fun k => mulByNat (omegaPowTree n) k)

/-
**Ordinal Power Realization**: `omegaPowTree n` has rank exactly `ω^n`.
-/

/-! ## Cluster G: Cantor Normal Form Realizability -/

/-- A CNF term is a pair `(coefficient, exponent)`. -/
def CNFTerm := ℕ × ℕ

/-- Evaluate a CNF list to its ordinal value.
Each term `(a, n)` contributes `ω^n * a` (the standard CNF convention). -/
def cnfValue : List CNFTerm → Ordinal
  | [] => 0
  | (a, n) :: rest => omega0 ^ (n : Ordinal) * (a : Ordinal) + cnfValue rest

/-- Build a tree realizing a CNF list.
Uses `prepend` to compose terms and `mulByNat`/`omegaPowTree` for individual terms. -/
def cnfTree : List CNFTerm → InfBranchTree
  | [] => .leaf
  | (a, n) :: rest => prepend (mulByNat (omegaPowTree n) a) (cnfTree rest)



/-
**CNF Realizability Theorem**: The rank of `cnfTree L` equals the
CNF ordinal value `cnfValue L`. This holds for all lists, not just valid CNFs.
-/

/-! ## Cluster H: ω^ω Realization -/

/-- `omegaToOmegaTree` is the canonical tree of rank `ω^ω`.
Its n-th child is `omegaPowTree n`, the tree of rank `ω^n`. -/
def omegaToOmegaTree : InfBranchTree :=
  .node (fun n => omegaPowTree n)

/-
Auxiliary: `⨆ n : ℕ, ω^n = ω^ω`
-/

/-
**ω^ω Realization Theorem**: `omegaToOmegaTree` has rank exactly `ω^ω`.
This is the first true limit-stage synthesis theorem: the tree formalism
can encode transfinite convergence of structural complexity.
-/

/-! ## Corollaries -/



end InfBranchTree

end


