-- Prove2me | solution 1 for UnitalMagmaDefect.defect_congr
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T14:43:04.305867+00:00
-- url     : https://prove2.me/submissions/8c80dc8c-08be-4bba-846b-62db5d2e5f2b

/-
# `UnitalMagmaDefect.defect_congr`
Target `dabcae54` (WA x3, CE x2). Gift: SAFE. Binders VERBATIM from its own WA — note `M` and `N` are
BOTH `Type ?u.3`, the SAME universe; writing `Type*` twice would generate two and fail the gate.

Transport the non-associative triples along `e` componentwise. `MulEquiv.map_mul` is PROTECTED
(Equiv/Defs.lean:230), and `e.injective` carries the disequality back.
-/
import Mathlib
import Definitions.Def_Combinatorics_UnitalMagmaDefect

set_option maxHeartbeats 800000

open UnitalMagmaDefect Finset

universe u

open UnitalMagmaDefect in
/-- **The target, verbatim.** -/
theorem solution {M N : Type u} [Mul M] [Mul N] [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N]
    (e : M ≃* N) : defect M = defect N := by
  classical
  let E : (M × M × M) ≃ (N × N × N) :=
    { toFun := fun t => (e t.1, e t.2.1, e t.2.2)
      invFun := fun t => (e.symm t.1, e.symm t.2.1, e.symm t.2.2)
      left_inv := by intro t; simp
      right_inv := by intro t; simp }
  simp only [defect, defectSet]
  refine Finset.card_equiv E ?_
  intro t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, E]
  constructor
  · intro hne heq
    exact hne (e.injective (by simpa [e.map_mul] using heq))
  · intro hne heq
    exact hne (by simpa [e.map_mul] using congrArg e heq)
