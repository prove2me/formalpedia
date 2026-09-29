-- Prove2me | solution 1 for UnitalMagmaDefect.defect_op
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T14:18:13.867766+00:00
-- url     : https://prove2.me/submissions/86e1ce58-853c-4ece-8dfd-ad4ea55b0af4

/-
# `UnitalMagmaDefect.defect_op`
Target `e94cdf50` (WA x3, CE x2). Gift: SAFE. Binders VERBATIM from its own WA:
`{M} [Mul M] [Fintype M] [DecidableEq M]` — the bundle supplies `Fintype Mᵐᵒᵖ` and `DecidableEq Mᵐᵒᵖ`
itself, which is why they do not appear.

`defect` counts NON-associative triples. In `Mᵐᵒᵖ` every product reverses — `unop (x*y) = unop y * unop x`
is `rfl` — so the non-associative triples correspond under `(x,y,z) ↦ (op z, op y, op x)`.
`Finset.card_equiv` needs only that equivalence and one membership iff.
-/
import Mathlib
import Definitions.Def_Combinatorics_UnitalMagmaDefect

set_option maxHeartbeats 800000

open UnitalMagmaDefect Finset

open UnitalMagmaDefect in
/-- **The target, verbatim.** -/
theorem solution {M : Type*} [Mul M] [Fintype M] [DecidableEq M] : defect Mᵐᵒᵖ = defect M := by
  classical
  let e : (Mᵐᵒᵖ × Mᵐᵒᵖ × Mᵐᵒᵖ) ≃ (M × M × M) :=
    { toFun := fun t => (MulOpposite.unop t.2.2, MulOpposite.unop t.2.1, MulOpposite.unop t.1)
      invFun := fun t => (MulOpposite.op t.2.2, MulOpposite.op t.2.1, MulOpposite.op t.1)
      left_inv := by intro t; simp
      right_inv := by intro t; simp }
  simp only [defect, defectSet]
  refine Finset.card_equiv e ?_
  intro t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, e]
  constructor
  · intro hne heq; exact hne (by simpa [MulOpposite.unop_mul] using congrArg MulOpposite.op heq.symm)
  · intro hne heq; exact hne (by simpa [MulOpposite.unop_mul] using congrArg MulOpposite.unop heq.symm)
