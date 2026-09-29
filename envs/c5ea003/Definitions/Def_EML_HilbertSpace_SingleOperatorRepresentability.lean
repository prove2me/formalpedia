-- Prove2me | Definitions.Def_EML_HilbertSpace_SingleOperatorRepresentability
-- name    : EML_HilbertSpace_SingleOperatorRepresentability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:33.072028+00:00
-- url     : https://prove2.me/theorems/21f29d09-d620-49e3-a1de-078c41db6754
-- title:
--   Aether Catalog definitions — EML_HilbertSpace_SingleOperatorRepresentability
-- statement:
--   Definition bundle for the Aether Catalog module `EML.HilbertSpace.SingleOperatorRepresentability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/HilbertSpace/SingleOperatorRepresentability.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# EML Single-Operator Representability: Core Grammar and Semantics

This file provides the foundational grammar and denotational semantics for the
**EML Single-Operator Church–Turing** program. We introduce two expression
languages over the reals in finitely many real variables:

* `EMLExpr`  — the *two-operator* elementary language with the field operations
  `+, ×, neg, inv`, real constants, variables, and **both** transcendental
  primitives `exp` and `log`.
* `EMLOnlyExpr` — the *single-operator* language with the same field operations,
  real constants, variables, and the **sole** transcendental primitive
  `eml(x, y) = exp(x) − log(y)`.

The thesis under investigation (formalised downstream in
`EML.SingleOperatorCompilation`) is that the single binary operator `eml`
generates exactly the same function class as the pair `{exp, log}` — a
"single-operator Church–Turing thesis" for the elementary real functions.

## Main definitions

* `EMLExpr`, `EMLExpr.eval`, `EMLExpr.size`
* `EMLOnlyExpr`, `EMLOnlyExpr.eval`, `EMLOnlyExpr.size`
* `EMLRepresentable`, `EMLOnlyRepresentable` — representability of a function
  `f : (Fin n → ℝ) → ℝ` in each language.

## Main results

* `EMLExpr.size_pos`, `EMLOnlyExpr.size_pos` — sizes are positive.
* `EMLOnlyExpr.eval_eml` — the defining identity of the `eml` node.
* `EMLOnlyExpr.exp_eq_eml_one`, `EMLOnlyExpr.log_eq_one_sub_eml` — `exp` and
  `log` are each recovered semantically from `eml`.
-/

noncomputable section

open Real

/-! ## §1. The two-operator language `EMLExpr` -/

/-- The two-operator EML grammar: field operations, constants, variables
    (indexed by `ℕ`), and the two transcendental primitives `exp` and `log`. -/
inductive EMLExpr : Type where
  | const (c : ℝ) : EMLExpr
  | var (n : ℕ) : EMLExpr
  | add (e₁ e₂ : EMLExpr) : EMLExpr
  | mul (e₁ e₂ : EMLExpr) : EMLExpr
  | neg (e : EMLExpr) : EMLExpr
  | inv (e : EMLExpr) : EMLExpr
  | exp (e : EMLExpr) : EMLExpr
  | log (e : EMLExpr) : EMLExpr
  deriving Inhabited

namespace EMLExpr

/-- Total denotational semantics for `EMLExpr` in an environment `env : ℕ → ℝ`.
    We use Mathlib's total junk-value conventions: `x⁻¹ = 0` at `0` and
    `Real.log x = 0` for `x ≤ 0`. -/
def eval : EMLExpr → (ℕ → ℝ) → ℝ
  | const c, _ => c
  | var n, env => env n
  | add e₁ e₂, env => e₁.eval env + e₂.eval env
  | mul e₁ e₂, env => e₁.eval env * e₂.eval env
  | neg e, env => -(e.eval env)
  | inv e, env => (e.eval env)⁻¹
  | exp e, env => Real.exp (e.eval env)
  | log e, env => Real.log (e.eval env)

/-- The number of nodes in an `EMLExpr` syntax tree. -/
def size : EMLExpr → ℕ
  | const _ => 1
  | var _ => 1
  | add e₁ e₂ => 1 + e₁.size + e₂.size
  | mul e₁ e₂ => 1 + e₁.size + e₂.size
  | neg e => 1 + e.size
  | inv e => 1 + e.size
  | exp e => 1 + e.size
  | log e => 1 + e.size



end EMLExpr

/-! ## §2. The single-operator language `EMLOnlyExpr` -/

/-- The single-operator EML grammar: field operations, constants, variables,
    and the *sole* transcendental primitive `eml(x, y) = exp(x) − log(y)`. -/
inductive EMLOnlyExpr : Type where
  | const (c : ℝ) : EMLOnlyExpr
  | var (n : ℕ) : EMLOnlyExpr
  | add (e₁ e₂ : EMLOnlyExpr) : EMLOnlyExpr
  | mul (e₁ e₂ : EMLOnlyExpr) : EMLOnlyExpr
  | neg (e : EMLOnlyExpr) : EMLOnlyExpr
  | inv (e : EMLOnlyExpr) : EMLOnlyExpr
  | eml (e₁ e₂ : EMLOnlyExpr) : EMLOnlyExpr
  deriving Inhabited

namespace EMLOnlyExpr

/-- Total denotational semantics for `EMLOnlyExpr`. The `eml` node realises
    `eml(x, y) = exp(x) − log(y)`. -/
def eval : EMLOnlyExpr → (ℕ → ℝ) → ℝ
  | const c, _ => c
  | var n, env => env n
  | add e₁ e₂, env => e₁.eval env + e₂.eval env
  | mul e₁ e₂, env => e₁.eval env * e₂.eval env
  | neg e, env => -(e.eval env)
  | inv e, env => (e.eval env)⁻¹
  | eml e₁ e₂, env => Real.exp (e₁.eval env) - Real.log (e₂.eval env)

/-- The number of nodes in an `EMLOnlyExpr` syntax tree. -/
def size : EMLOnlyExpr → ℕ
  | const _ => 1
  | var _ => 1
  | add e₁ e₂ => 1 + e₁.size + e₂.size
  | mul e₁ e₂ => 1 + e₁.size + e₂.size
  | neg e => 1 + e.size
  | inv e => 1 + e.size
  | eml e₁ e₂ => 1 + e₁.size + e₂.size






end EMLOnlyExpr

/-! ## §3. Representability -/

/-- The canonical environment associated to a point `x : Fin n → ℝ`:
    variable `i` reads coordinate `i` when `i < n`, and is `0` otherwise. -/
def emlEnv {n : ℕ} (x : Fin n → ℝ) : ℕ → ℝ :=
  fun i => if h : i < n then x ⟨i, h⟩ else 0




end


