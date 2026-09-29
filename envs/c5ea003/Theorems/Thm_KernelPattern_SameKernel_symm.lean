-- Prove2me | Theorems.Thm_KernelPattern_SameKernel_symm
-- name    : KernelPattern.SameKernel.symm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:39:47.487255+00:00
-- url     : https://prove2.me/theorems/177144c9-9327-46fb-8baa-e6b9c95d7534
-- title:
--   Symm
-- statement:
--   Formal statement of `KernelPattern.SameKernel.symm` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem KernelPattern.SameKernel.symm{x : Fin n → α} {y : Fin n → β} (h : SameKernel x y) :
--       SameKernel y x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/KernelPatterns/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/KernelPatterns/Core.lean#L36

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

theorem KernelPattern.SameKernel.symm{x : Fin n → α} {y : Fin n → β} (h : SameKernel x y) :
    SameKernel y x := by sorry
