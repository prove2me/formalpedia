-- Prove2me | Theorems.Thm_Geometry_KernelPatterns_exists_perm_of_pat_eq
-- name    : Geometry.KernelPatterns.exists_perm_of_pat_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:21:30.448859+00:00
-- url     : https://prove2.me/theorems/2a0ff8ff-0811-488a-9917-1d11b0123a95
-- title:
--   If two tuples over a finite type have equal patterns then some permutation
-- statement:
--   If two tuples over a finite type have equal patterns then some permutation
--   of the value type carries one to the other.
--
--   ```lean
--   theorem Geometry.KernelPatterns.exists_perm_of_pat_eq{x y : Fin n → X} (h : pat x = pat y) :
--       ∃ σ : Equiv.Perm X, σ ∘ x = y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KernelPatterns/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KernelPatterns/Core.lean#L96

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

theorem Geometry.KernelPatterns.exists_perm_of_pat_eq{x y : Fin n → X} (h : pat x = pat y) :
    ∃ σ : Equiv.Perm X, σ ∘ x = y := by sorry
