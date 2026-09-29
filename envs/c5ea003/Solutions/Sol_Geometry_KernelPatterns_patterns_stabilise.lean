-- Prove2me | solution 1 for Geometry.KernelPatterns.patterns_stabilise
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:15:57.634143+00:00
-- url     : https://prove2.me/submissions/9f4e4580-5081-499d-9f6e-d0008da4b55b

-- Sol generated from Geometry/KernelPatterns/Core.lean
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






open Geometry.KernelPatterns in
theorem solution{n m : ℕ} (h : n ≤ m) : patterns n m = patterns n n := by
  ext p
  rw [mem_patterns_iff, mem_patterns_self]
  refine ⟨fun hp => hp.1, fun hp => ⟨hp, le_trans (by simpa using Finset.card_le_univ (univ.image p)) h⟩⟩
