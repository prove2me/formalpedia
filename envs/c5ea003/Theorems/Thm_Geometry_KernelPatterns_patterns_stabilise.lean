-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_patterns_stabilise
-- name    : Geometry.KernelPatterns.patterns_stabilise
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:22:20.02507+00:00
-- url     : https://prove2.me/theorems/90decca2-01f1-4067-8d43-561f45e3b948
-- title:
--   Stabilisation: once there are at least `n` available values, the set of
-- statement:
--   **Stabilisation**: once there are at least `n` available values, the set of
--   kernel patterns of `n`-tuples no longer depends on the value type.
--
--   ```lean
--   theorem Geometry.KernelPatterns.patterns_stabilise{n m : ℕ} (h : n ≤ m) : patterns n m = patterns n n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/Core.lean#L198

-- Thm stub generated from Geometry/KernelPatterns/Core.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Core

/-!
# Kernel patterns of tuples: a complete invariant for the symmetric-group action

For a tuple `x : Fin n → X` its *kernel* is the equivalence relation
`i ~ j ↔ x i = x j` on the index set `Fin n`.  We encode it by the canonical
*pattern* `pat x : Fin n → Fin n`, sending `i` to the least index `j` with
`x j = x i` (the "first occurrence" representative).

Main results of this file.

* `pat_eq_iff` — `pat` faithfully records the kernel.
* `pat_congr`, `pat_comp_injective` — `pat` is invariant under post-composition
  by injective maps, in particular under the diagonal action of `Equiv.Perm X`.
* `exists_perm_of_pat_eq`, `perm_orbit_iff_pat_eq` — for a *finite* value type
  `X`, equality of patterns is *exactly* equality of `Sym(X)`-orbits, i.e. the
  kernel is a complete invariant of the symmetric-group action on `X ^ n`.
* `pat_not_complete_of_trivial_group` — sharpness: for a proper subgroup the
  kernel need not be a complete invariant.
* `pat_idem`, `mem_patterns_iff` — patterns are exactly the idempotent tuples
  `p : Fin n → Fin n` with `pat p = p`; consequently the set of patterns
  *stabilises*: `patterns n m = patterns n n` as soon as `n ≤ m`
  (`patterns_stabilise`).
-/

open Geometry.KernelPatterns

open Finset

variable {n : ℕ} {X Y : Type*}


variable [DecidableEq X]












/-! ### Completeness of the invariant for the symmetric group -/


variable [Fintype X] [DecidableEq X]





/-! ### The set of patterns, and stabilisation -/

theorem Geometry.KernelPatterns.patterns_stabilise{n m : ℕ} (h : n ≤ m) : patterns n m = patterns n n := by sorry
