-- Prove2me | Definitions.Def_Bridges_SparseMatrixStructure_SparseMatrixStructure
-- name    : Bridges_SparseMatrixStructure_SparseMatrixStructure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:44.081441+00:00
-- url     : https://prove2.me/theorems/134bb321-ccf7-41d6-967a-a476984d9242
-- title:
--   Aether Catalog definitions — Bridges_SparseMatrixStructure_SparseMatrixStructure
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.SparseMatrixStructure.SparseMatrixStructure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/SparseMatrixStructure/SparseMatrixStructure.lean by skeleton subtraction
import Mathlib

/-!
# Sparse Matrix Structure Preservation under Tensor Rewrites

## Overview

This file formalizes a **support-sensitive denotational invariant** for a three-sorted
tensor rewrite calculus with sorts `{Scal, Vec, Mat}`. While semantic correctness
(preservation of denotation under rewrites) is established in `TensorSortedRewrite.lean`,
this file proves a qualitatively stronger property: rewriting preserves a computable
*row-sparsity bound*.

The key mathematical insight is that the distributive rewrite system cannot introduce
qualitatively new fill-in. Addition is the only source of support growth (additive),
while scalar multiplication preserves support exactly (for nonzero scalars).

## Main results

- `RowSparse.add`: row-`s`-sparse + row-`t`-sparse ⟹ row-`(s+t)`-sparse (Theorem 1)
- `RowSparse.smul`: scalar mult preserves row sparsity (Theorem 2)
- `rowSupport_smul_eq`: nonzero scalar preserves row support exactly (Theorem 2')
- `evalMat_rowSparse_bound`: semantic support bound via `matLeafCount` (Theorem 3)
- `rewrite_preserves_matLeafCount`: one-step mat rewrite preserves leaf count (Theorem 4)
- `normStepMat_preserves_matLeafCount`: normalization preserves leaf count (Theorem 5a)
- `normalize_rowSparse_bound`: normalization inherits support bound (Theorem 5)
- `rowSupport_add_eq_of_disjoint`: exact support under disjoint entries (Theorem 6)
-/

open Finset Matrix BigOperators

namespace SparseMatrix

/-! ## Part 0: Self-contained fragment of the tensor rewrite calculus -/

/-- The three sorts of the tensor calculus. -/
inductive TSort | scal | vec | mat
  deriving DecidableEq

/-- Terms of the tensor language, indexed by sort. -/
inductive TTerm : TSort → Type
  | scalVar  : ℕ → TTerm .scal
  | vecVar   : ℕ → TTerm .vec
  | matVar   : ℕ → TTerm .mat
  | scalAdd  : TTerm .scal → TTerm .scal → TTerm .scal
  | scalMul  : TTerm .scal → TTerm .scal → TTerm .scal
  | vecAdd   : TTerm .vec → TTerm .vec → TTerm .vec
  | matAdd   : TTerm .mat → TTerm .mat → TTerm .mat
  | smulVec  : TTerm .scal → TTerm .vec → TTerm .vec
  | smulMat  : TTerm .scal → TTerm .mat → TTerm .mat
  | mulVec   : TTerm .mat → TTerm .vec → TTerm .vec
  | dot      : TTerm .vec → TTerm .vec → TTerm .scal

/-- Semantic environment. -/
structure TEnv (R : Type*) (n : ℕ) where
  scalAssign : ℕ → R
  vecAssign  : ℕ → (Fin n → R)
  matAssign  : ℕ → Matrix (Fin n) (Fin n) R

variable {R : Type*} {n : ℕ} [CommRing R]

mutual
noncomputable def evalScal (env : TEnv R n) : TTerm .scal → R
  | .scalVar k    => env.scalAssign k
  | .scalAdd a b  => evalScal env a + evalScal env b
  | .scalMul a b  => evalScal env a * evalScal env b
  | .dot v w      => ∑ i : Fin n, evalVec env v i * evalVec env w i
noncomputable def evalVec (env : TEnv R n) : TTerm .vec → (Fin n → R)
  | .vecVar k    => env.vecAssign k
  | .vecAdd v w  => evalVec env v + evalVec env w
  | .smulVec a v => evalScal env a • evalVec env v
  | .mulVec A v  => Matrix.mulVec (evalMat env A) (evalVec env v)
noncomputable def evalMat (env : TEnv R n) : TTerm .mat → Matrix (Fin n) (Fin n) R
  | .matVar k    => env.matAssign k
  | .matAdd A B  => evalMat env A + evalMat env B
  | .smulMat a A => evalScal env a • evalMat env A
end

/-- One-step normalization for mat-sorted terms. -/
def normStepMat : TTerm .mat → TTerm .mat
  | .smulMat a (.matAdd A B) => .matAdd (.smulMat a A) (.smulMat a B)
  | t => t


/-- The mat-sorted rewrite rule. -/
inductive MatRewrite : TTerm .mat → TTerm .mat → Prop
  | smulMat_matAdd (a : TTerm .scal) (A B : TTerm .mat) :
      MatRewrite (.smulMat a (.matAdd A B)) (.matAdd (.smulMat a A) (.smulMat a B))

/-! ## Section 1: Row Support and Row Sparsity -/

variable [DecidableEq R]

/-- Row support of matrix `A` at row `i`. -/
def rowSupport (A : Matrix (Fin n) (Fin n) R) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => A i j ≠ 0)

/-- A matrix is **row-`s`-sparse** if every row has at most `s` nonzero entries. -/
def RowSparse (s : ℕ) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i : Fin n, (rowSupport A i).card ≤ s

/-- Environment row-sparsity. -/
def EnvRowSparse (ρ : ℕ → Matrix (Fin n) (Fin n) R) (s : ℕ) : Prop :=
  ∀ x, RowSparse s (ρ x)

/-- Row-disjoint matrices. -/
def RowDisjoint (A B : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, A i j ≠ 0 → B i j = 0

/-! ## Section 2: Support Containment Lemmas -/




/-! ## Section 3: Core Sparsity Theorems -/





/-! ## Section 4: Exact Support under Disjoint Entries -/


/-! ## Section 5: Syntactic Sparsity Budget -/

/-- Matrix leaf count — the sparsity budget multiplier. -/
def matLeafCount : TTerm .mat → ℕ
  | .matVar _ => 1
  | .matAdd A B => matLeafCount A + matLeafCount B
  | .smulMat _ A => matLeafCount A


/-! ## Section 6: Rewrite-Step Invariance -/


/-! ## Section 7: Normalization -/



end SparseMatrix


