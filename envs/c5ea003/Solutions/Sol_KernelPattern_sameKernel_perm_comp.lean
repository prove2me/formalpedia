-- Prove2me | solution 1 for KernelPattern.sameKernel_perm_comp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:04:50.57256+00:00
-- url     : https://prove2.me/submissions/9c5323e0-ea8d-4d2d-808a-15e4c155b22e

-- Sol generated from Algebra/KernelPatterns/Core.lean
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






open KernelPattern in
omit [DecidableEq α] in
theorem solution(σ : Equiv.Perm α) (x : Fin n → α) : SameKernel (σ ∘ x) x :=
  fun _ _ => ⟨fun h => σ.injective h, fun h => congrArg σ h⟩
