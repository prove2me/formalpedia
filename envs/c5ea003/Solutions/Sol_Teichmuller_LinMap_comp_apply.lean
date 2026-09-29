-- Prove2me | solution 1 for Teichmuller.LinMap.comp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T05:14:31.482178+00:00
-- url     : https://prove2.me/submissions/3227482a-43b2-4ad7-a2a8-155f0d282ad1

/-
# `Teichmuller.LinMap.comp_apply`
Target `952e7acd` (Open, not deprecated at draft time; re-read live immediately before submitting).

NOT YET COMPILED — drafted while the build lock was held by another ship.

ORDINARY PROOF — imports nothing from `Theorems`, so no `sorryAx` and no axiom audit.

`toFun z = a·z + b·conj z`, and `comp` is defined by
    (f.comp g).a = f.a·g.a + f.b·conj g.b        (f.comp g).b = f.a·g.b + f.b·conj g.a
Expanding both sides gives the SAME four terms:
    RHS = f.a·(g.a z + g.b conj z) + f.b·conj(g.a z + g.b conj z)
        = f.a g.a z + f.a g.b conj z + f.b conj(g.a) conj z + f.b conj(g.b) z
    LHS = (f.a g.a + f.b conj g.b)·z + (f.a g.b + f.b conj g.a)·conj z
The only non-ring steps are pushing `conj` through a sum and a product, and `conj (conj z) = z`.

Verified numerically: worst absolute difference 2.2e-14 over random maps. It also holds with
UNCONSTRAINED coefficients — 4000 trials, no counterexamples — so `norm_lt` is carried by the
structure but plays no part in this identity. That is worth knowing: no positivity or
non-vanishing side condition can be lurking.
-/
import Mathlib
import Definitions.Def_Geometry_Teichmuller_LinearQC

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Teichmuller in
/-- **The target, verbatim.** -/
theorem solution (f g : LinMap) (z : ℂ) : (f.comp g).toFun z = f.toFun (g.toFun z) := by
  simp only [LinMap.toFun, LinMap.comp, map_add, map_mul, Complex.conj_conj]
  ring
