-- Prove2me | Definitions.Def_Bridges_TropicalNormalization
-- name    : Bridges_TropicalNormalization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:47.362357+00:00
-- url     : https://prove2.me/theorems/761ff237-fb4f-45ae-ba70-1ae28a900f27
-- title:
--   Aether Catalog definitions — Bridges_TropicalNormalization
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalNormalization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalNormalization.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Expression Normalization: A Verified Tactic Kernel

This file implements a certified normalizer for tropical (min-plus) expressions over ℝ.
We define:
- `TropExpr`: a small expression language with constants, variables, min, and addition
- `eval`: semantic evaluation in an environment
- `size`: syntactic complexity measure
- `normalize`: a recursive normalizer performing constant folding and idempotence elimination

We prove the following main theorems:
1. `normalize_preserves_semantics`: normalization preserves evaluation semantics
2. `normalize_nonincreasing_size`: normalization does not increase expression size
3. `normalize_idempotent`: normalization is idempotent (a closure operator)
4. `normalize_isNormalized`: normalization outputs normal forms
5. `normalize_certified`: the combined certified normalizer theorem

Together these constitute a **verified tactic kernel**: an executable normalization
procedure with machine-checked correctness, suitable as the trusted core of
proof-producing automation for tropical algebra.
-/


open Classical

noncomputable section

/-! ## Expression Language -/

/-- A tropical expression over ℝ with constants, variables, min, and addition. -/
inductive TropExpr where
  | const : ℝ → TropExpr
  | var   : ℕ → TropExpr
  | tmin  : TropExpr → TropExpr → TropExpr
  | add   : TropExpr → TropExpr → TropExpr

namespace TropExpr

instance : DecidableEq TropExpr := fun a b => Classical.dec (a = b)

/-! ## Semantic Evaluation -/

/-- Evaluate a tropical expression in environment `σ`. -/
def eval (σ : ℕ → ℝ) : TropExpr → ℝ
  | .const r   => r
  | .var n     => σ n
  | .tmin a b  => min (eval σ a) (eval σ b)
  | .add a b   => eval σ a + eval σ b

/-! ## Syntactic Complexity -/

/-- Size of a tropical expression (number of nodes). -/
def size : TropExpr → Nat
  | .const _   => 1
  | .var _     => 1
  | .tmin a b  => size a + size b + 1
  | .add a b   => size a + size b + 1

/-! ## Normalization -/

/-- Normalize a tropical expression by constant folding and idempotence elimination. -/
def normalize : TropExpr → TropExpr
  | .const r => .const r
  | .var n => .var n
  | .add a b =>
      let a' := normalize a
      let b' := normalize b
      match a', b' with
      | .const x, .const y => .const (x + y)
      | _, _ => .add a' b'
  | .tmin a b =>
      let a' := normalize a
      let b' := normalize b
      if a' = b' then a'
      else
        match a', b' with
        | .const x, .const y => .const (min x y)
        | _, _ => .tmin a' b'

/-! ## Normal Form Predicate -/

/-- A predicate recognizing expressions in normal form. -/
def isNormalized : TropExpr → Bool
  | .const _ => true
  | .var _ => true
  | .add (.const _) (.const _) => false
  | .add a b => isNormalized a && isNormalized b
  | .tmin a b =>
      if a = b then false
      else match a, b with
        | .const _, .const _ => false
        | _, _ => isNormalized a && isNormalized b

/-! ## Main Theorems -/

/-
Normalization preserves semantic evaluation.
-/

/-
Normalization does not increase expression size.
-/


/-
Normalization is idempotent: normalizing twice equals normalizing once.
-/

/-
Normalization produces expressions in normal form.
-/


/-
Extensional uniqueness: expressions with the same normal form have the same semantics.
-/

/-! ## One-Step Rewrite Soundness -/

/-- A single rewrite step applied at the top level. -/
def rewriteStep : TropExpr → TropExpr
  | .tmin (.const x) (.const y) => .const (min x y)
  | .add (.const x) (.const y) => .const (x + y)
  | .tmin a b => if a = b then a else .tmin a b
  | e => e

/-
One-step rewriting preserves semantics.
-/

/-! ## Semantic Bounds Preservation -/

/-
Normalization preserves any upper bound on evaluation.
-/

end TropExpr

end


