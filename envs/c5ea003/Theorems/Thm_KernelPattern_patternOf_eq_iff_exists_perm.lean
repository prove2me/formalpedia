-- Prove2me | Theorems.Thm_KernelPattern_patternOf_eq_iff_exists_perm
-- name    : KernelPattern.patternOf_eq_iff_exists_perm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:40:33.0782+00:00
-- url     : https://prove2.me/theorems/868196e1-a595-4e37-9db4-aca9f8393f66
-- title:
--   `patternOf` is a complete invariant for the `Equiv.Perm α`-action.
-- statement:
--   `patternOf` is a complete invariant for the `Equiv.Perm α`-action.
--
--   ```lean
--   theorem KernelPattern.patternOf_eq_iff_exists_perm[Finite α] {x y : Fin n → α} :
--       patternOf x = patternOf y ↔ ∃ σ : Equiv.Perm α, σ ∘ x = y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/KernelPatterns/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/KernelPatterns/Core.lean#L216

-- Thm stub generated from Algebra/KernelPatterns/Core.lean
import Mathlib
import Definitions.Def_Algebra_KernelPatterns_Core
/-
# Kernel patterns of tuples: canonical form, invariance and completeness

For a tuple `x : Fin n → α` the *kernel* (or *equality pattern*) of `x` is the
equivalence relation `i ~ j ↔ x i = x j` on the index set `Fin n`.  This file
develops a computable canonical form for the kernel,

`canon x i = min { j | x j = x i }`,

and proves the two facts that make the kernel a *complete invariant* for the
action of the symmetric group `Equiv.Perm α` on tuples by postcomposition:

* `KernelPattern.canon_comp_of_injective` — the kernel is invariant: relabelling
  the values by an injection (in particular by a permutation) does not change it;
* `KernelPattern.sameKernel_iff_exists_perm` — the kernel is complete: two tuples
  with the same kernel differ by a permutation of `α`.

We also characterise the range of `canon` as the set of *idempotent contracting
retractions* `p : Fin n → Fin n` (`p i ≤ i` and `p (p i) = p i`), i.e. the
restricted-growth encodings of set partitions, and package it as the type
`KernelPattern.Pattern n`, which is a `Fintype` with decidable equality.
-/

open KernelPattern

variable {α β : Type*} {n : ℕ}

/-! ## The kernel relation -/







/-! ## The canonical form -/


variable [DecidableEq α] [DecidableEq β]









/-! ## Invariance under relabelling of the values -/



/-! ## Completeness of the invariant -/


/-! ## Patterns: the range of `canon` -/






instance : Fintype (Pattern n) := Subtype.fintype _

theorem KernelPattern.patternOf_eq_iff_exists_perm[Finite α] {x y : Fin n → α} :
    patternOf x = patternOf y ↔ ∃ σ : Equiv.Perm α, σ ∘ x = y := by sorry
