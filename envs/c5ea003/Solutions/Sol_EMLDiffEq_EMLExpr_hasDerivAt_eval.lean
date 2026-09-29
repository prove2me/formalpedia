-- Prove2me | solution 1 for EMLDiffEq.EMLExpr.hasDerivAt_eval
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T13:01:44.878049+00:00
-- url     : https://prove2.me/submissions/422fdff1-4654-43a1-91e4-2d90055b08b1

import Mathlib
import Definitions.Def_Applications_EML_EMLDifferentialEquations
open EMLDiffEq EMLDiffEq.EMLExpr in
theorem solution : ∀ (e : EMLExpr) (x : ℝ), Regular e x →
    HasDerivAt (eval e) (eval (D e) x) x := by
  intro e
  induction e with
  | X => intro x _; exact hasDerivAt_id x
  | const c => intro x _; exact hasDerivAt_const x c
  | add a b iha ihb => intro x h; exact (iha x h.1).add (ihb x h.2)
  | mul a b iha ihb => intro x h; exact (iha x h.1).mul (ihb x h.2)
  | inv a iha =>
    intro x h
    have h0 : eval a x ≠ 0 := h.2
    have := (iha x h.1).inv h0
    convert this using 1
    show -1 * (eval (D a) x * ((eval a x)⁻¹ * (eval a x)⁻¹)) = -eval (D a) x / eval a x ^ 2
    field_simp
  | exp a iha =>
    intro x h
    have := (iha x h).exp
    convert this using 1
    show eval (D a) x * Real.exp (eval a x) = _
    ring
  | log a iha =>
    intro x h
    have h0 : eval a x ≠ 0 := h.2
    have := (iha x h.1).log h0
    convert this using 1
