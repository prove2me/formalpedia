-- Prove2me | Definitions.Def_Applications_TuringJumpHierarchy
-- name    : Applications_TuringJumpHierarchy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:57:20.108701+00:00
-- url     : https://prove2.me/theorems/5ceebd6b-d8e5-4622-aca2-ecd06610831e
-- title:
--   Aether Catalog definitions — Applications_TuringJumpHierarchy
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.TuringJumpHierarchy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/TuringJumpHierarchy.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Oracle's Burden, Part II: The abstract Turing-jump hierarchy

Building on Mathlib's `TuringDegree`, we axiomatize the **Turing jump** operator `J` by its two
defining order-theoretic properties and prove that iterating *any* such operator produces a
strictly increasing `ω`-chain of Turing degrees

  `A  <ᵀ  J A  <ᵀ  J² A  <ᵀ  J³ A  <ᵀ  ...`

which is the computability-theoretic incarnation of the theory tower

  `PA  <  PA^H  <  PA^{H^H}  <  ...`.

This isolates the *combinatorial skeleton* of the hierarchy from the (much heavier) construction
of a concrete jump via a relativized universal machine.  The canonical model of `IsJump` is the
Turing jump `A ↦ A'`, whose two axioms — `A ≤ᵀ A'` and `¬ A' ≤ᵀ A` — are Post's relativized
halting theorem; the base instance `0 <ᵀ 0'` is proved unconditionally in
`Computation.OracleHierarchy` (`exists_degree_gt_zero`).

The mission's slogan — *proves its own consistency but cannot decide its own soundness* — is
exactly `A <ᵀ J A`: the jump `J A` decides the halting behaviour of every `A`-machine
("consistency of the level below"), yet `A` cannot decide membership in `J A`
("its own soundness").  Non-idempotence of the jump (`jump_not_idempotent`) says this burden
strictly recurs at every level: no amount of oracle knowledge ever makes the next jump free.

## Main results

* `IsJump` — the two axioms of an abstract jump operator.
* `IsJump.lt` — one jump strictly increases the degree: `A <ᵀ J A`.
* `IsJump.hierarchy_strictMono` — the iterated hierarchy is strictly increasing.
* `IsJump.hierarchy_lt` — `Jᵐ A <ᵀ Jⁿ A` whenever `m < n`.
* `IsJump.hierarchyEmbedding` — the hierarchy is an **order embedding** `(ℕ, <) ↪o TuringDegree`,
  i.e. the oracle hierarchy is order-isomorphic to the standard `ω`-indexed Turing-jump hierarchy.
* `IsJump.hierarchy_injective` — all levels are pairwise distinct degrees.
* `jump_not_idempotent` — a **disproof** of "the jump is idempotent": `J (J A) ≢ᵀ J A`.
* `not_isJump_id`, `not_isJump_const` — the `IsJump` axioms are **discriminating**: no trivial
  operator (identity or constant) is a jump.

## Contrarian log

* CONJECTURE: the jump stabilizes, i.e. `J (J A) ≡ᵀ J A` for some/all `A`.
  **DISPROVED** by `jump_not_idempotent`.
* CONJECTURE: the hierarchy `A, J A, J² A, ...` eventually repeats a degree.
  **DISPROVED** by `IsJump.hierarchy_injective`.
* CONJECTURE: the identity / a constant map could serve as a jump operator.
  **DISPROVED** by `not_isJump_id` and `not_isJump_const`.
-/


open scoped Computability
open Primrec Nat.Partrec Part

namespace TuringJumpHierarchy

/-- The Turing degree of a partial function. -/
noncomputable def tdeg (f : ℕ →. ℕ) : TuringDegree := Quotient.mk _ f


/-- An **abstract Turing jump**: an operator `J` on partial functions such that
* every function is computable from its jump (`le`), and
* no function computes its own jump (`not_ge`).

The canonical instance is the Turing jump `A ↦ A'`; these two axioms are precisely the content of
the relativized halting theorem. -/
structure IsJump (J : (ℕ →. ℕ) → (ℕ →. ℕ)) : Prop where
  /-- The oracle is recursive in its own jump. -/
  le : ∀ A, A ≤ᵀ J A
  /-- The jump is *not* recursive in the oracle: it is a genuine increase in power. -/
  not_ge : ∀ A, ¬ (J A ≤ᵀ A)

variable {J : (ℕ →. ℕ) → (ℕ →. ℕ)}








/-! ## The axiomatization has content: trivial operators are never jumps

The results above are stated for an arbitrary operator satisfying `IsJump`.  To show this is a
*discriminating* hypothesis — and not one satisfied by degenerate operators — we record that no
operator which fixes some oracle up to Turing equivalence can be a jump.  In particular the
identity and every constant operator fail to be jumps: a genuine jump must strictly increase power
at every oracle. -/




/-! ## Further consequences: inexhaustibility of the hierarchy -/

/-
Whenever an abstract jump exists, the Turing degrees have no maximal element: every oracle
has a strictly more powerful oracle, namely its jump.
-/

/-
No tail of the jump hierarchy is constant. Thus it cannot stabilize after finitely many
oracle additions.
-/

/-
Above every specified level there is a later, strictly stronger level.
-/

end TuringJumpHierarchy


