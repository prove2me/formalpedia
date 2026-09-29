-- Prove2me | solution 1 for GaloisConnectionFixedPoints.cl_monotone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:00:18.71861+00:00
-- url     : https://prove2.me/submissions/21d1322c-66ce-4bab-a133-562a3ee7ad41

-- Sol generated from Bridges/PosetTheory/GaloisConnectionFixedPoints.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_GaloisConnectionFixedPoints

/-!
# The order-theoretic half of the Galois-connection bridge

This file develops, **independently of Knaster–Tarski**, the fixed-point theory
attached to a Galois connection between two complete lattices.

Given complete lattices `α`, `β` and maps `l : α → β`, `u : β → α` forming a
Galois connection (`l a ≤ b ↔ a ≤ u b`), we:

* define the closure operator `cl a = u (l a)` on `α` and the kernel/interior
  operator `ker b = l (u b)` on `β`;
* prove the standard consequences of the adjunction *directly* from the
  defining bi-implication (`l`, `u` monotone; `a ≤ u (l a)`; `l (u b) ≤ b`;
  `u (l (u b)) = u b`; `l (u (l a)) = l a`);
* introduce the closed elements `{a // u (l a) = a}` and coclosed elements
  `{b // l (u b) = b}`;
* establish the fundamental fixed-point correspondence as an `OrderIso`
  (`fixedPointOrderIso`);
* prove that the closed elements form a complete lattice and the coclosed
  elements form a complete lattice, *without invoking Knaster–Tarski*,
  using only the closure-system structure (arbitrary infima of closed elements
  are closed; arbitrary suprema are obtained by closing the ambient supremum,
  and dually for coclosed elements);
* record the equivalent explicit least-upper-bound / greatest-lower-bound
  theorems with their closed-form witnesses.

**Anti-circularity.**  Nothing here references `Bridges.KnasterTarskiBridge`.
The bridge to Knaster–Tarski (least fixed point of `cl` is `u (l ⊥)`, greatest
fixed point of `ker` is `l (u ⊤)`) lives in the separate file
`Bridges.GaloisConnectionKnasterTarskiBridge`.
-/

open GaloisConnectionFixedPoints

universe u v

variable {α : Type u} {β : Type v}

/-! ## Section 1: the closure and kernel operators -/






/-! ## Section 2: consequences of the adjunction, proved directly -/


variable [CompleteLattice α] [CompleteLattice β] {l : α → β} {u : β → α}







/-! ### The closure / kernel operators are genuine closure / interior operators -/







/-! ## Section 3 & 4: closed / coclosed elements and the fixed-point `OrderIso` -/






/-! ## Section 5: the closed elements form a complete lattice

We use the closure-system structure rather than Knaster–Tarski:

* arbitrary infima of closed elements are closed (`closed_sInf_closed`);
* a least closed upper bound of a family is the closure of its ambient
  supremum (`closed_isLeastUB`).

The complete-lattice instance is then obtained from `completeLatticeOfInf`,
which only requires that every set of closed elements has an infimum that is a
greatest lower bound. -/





/-! ## Section 6: the coclosed elements form a complete lattice (dual) -/







open GaloisConnectionFixedPoints in
theorem solution(gc : GaloisConnection l u) : Monotone (cl l u) :=
  fun _ _ h => monotone_u gc (monotone_l gc h)
