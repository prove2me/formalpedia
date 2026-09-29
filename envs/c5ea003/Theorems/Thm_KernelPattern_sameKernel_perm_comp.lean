-- Prove2me | Theorems.Thm_KernelPattern_sameKernel_perm_comp
-- name    : KernelPattern.sameKernel_perm_comp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:40:23.102285+00:00
-- url     : https://prove2.me/theorems/55ff6c56-0d96-4796-823a-150f00eab247
-- title:
--   The kernel is an `Equiv.Perm α`-invariant of tuples.
-- statement:
--   The kernel is an `Equiv.Perm α`-invariant of tuples.
--
--   ```lean
--   theorem KernelPattern.sameKernel_perm_comp(σ : Equiv.Perm α) (x : Fin n → α) : SameKernel (σ ∘ x) x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/KernelPatterns/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/KernelPatterns/Core.lean#L132

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


omit [DecidableEq α] in

theorem KernelPattern.sameKernel_perm_comp(σ : Equiv.Perm α) (x : Fin n → α) : SameKernel (σ ∘ x) x := by sorry
