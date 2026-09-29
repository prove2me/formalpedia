-- Prove2me | Definitions.Def_Logic_CubicalSemantics_UniverseCodes
-- name    : Logic_CubicalSemantics_UniverseCodes
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:52:37.960987+00:00
-- url     : https://prove2.me/theorems/1eb8158f-6c03-4de5-b6ee-43d76475d08b
-- title:
--   Aether Catalog definitions — Logic_CubicalSemantics_UniverseCodes
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.CubicalSemantics.UniverseCodes`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/CubicalSemantics/UniverseCodes.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Universe Codes and Weak Univalence

This file constructs a small universe of codes for finite types and proves a
**weak univalence principle**: equivalence of interpretations implies equality of
normalized codes.

## Main definitions

- `UCode` — Inductive codes for finite types
- `El` — Interpretation function mapping codes to types
- `card` — Cardinality function on codes
- `canonical` — Canonical representative code for each natural number
- `normalize` — Normalization of codes to canonical form

## Main results

- `card_canonical` — The cardinality of a canonical code equals its index
- `normalize_idempotent` — Normalization is idempotent
- `canonical_injective` — Canonical codes are injective
- `fintypeEl` — Every interpreted code is a `Fintype`
- `decidableEqEl` — Every interpreted code has decidable equality
- `card_eq_fintype_card` — `card` agrees with `Fintype.card`
- `El_normalize_equiv` — A code's interpretation is equivalent to its normalization's
- `equiv_implies_card_eq` — Equivalent types have equal cardinality
- `weak_univalence_normalized` — Equivalent normal forms are equal codes
-/

namespace CubicalSemantics

-- Inline PathOver for self-containedness (main definition is in Basic.lean)

/-- Codes for a small universe of finite types. -/
inductive UCode : Type where
  | zero : UCode
  | one  : UCode
  | bool : UCode
  | sum  : UCode → UCode → UCode
  | prod : UCode → UCode → UCode
  deriving DecidableEq, Repr

/-- Interpretation of universe codes as Lean types. -/
def El : UCode → Type
  | .zero     => Empty
  | .one      => Unit
  | .bool     => Bool
  | .sum a b  => El a ⊕ El b
  | .prod a b => El a × El b

/-- Cardinality of a universe code. -/
def card : UCode → ℕ
  | .zero     => 0
  | .one      => 1
  | .bool     => 2
  | .sum a b  => card a + card b
  | .prod a b => card a * card b

/-- Canonical code for a given natural number. -/
def canonical : ℕ → UCode
  | 0     => .zero
  | 1     => .one
  | n + 2 => .sum .one (canonical (n + 1))

/-- Normalize a code to canonical form. -/
def normalize (c : UCode) : UCode := canonical (card c)


/-! ### Cardinality of canonical codes -/


/-! ### Normalization properties -/



/-! ### Fintype and DecidableEq instances for El -/

noncomputable instance fintypeEl : (c : UCode) → Fintype (El c)
  | .zero => (inferInstance : Fintype Empty)
  | .one => (inferInstance : Fintype Unit)
  | .bool => (inferInstance : Fintype Bool)
  | .sum a b => @instFintypeSum _ _ (fintypeEl a) (fintypeEl b)
  | .prod a b => @instFintypeProd _ _ (fintypeEl a) (fintypeEl b)

instance decidableEqEl : (c : UCode) → DecidableEq (El c)
  | .zero => (inferInstance : DecidableEq Empty)
  | .one => (inferInstance : DecidableEq Unit)
  | .bool => (inferInstance : DecidableEq Bool)
  | .sum a b => @instDecidableEqSum _ _ (decidableEqEl a) (decidableEqEl b)
  | .prod a b => @instDecidableEqProd _ _ (decidableEqEl a) (decidableEqEl b)

/-! ### Cardinality agreement -/


/-! ### Equivalences -/





end CubicalSemantics


