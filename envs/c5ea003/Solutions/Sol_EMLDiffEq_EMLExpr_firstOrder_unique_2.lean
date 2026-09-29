-- Prove2me | solution 2 for EMLDiffEq.EMLExpr.firstOrder_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T12:56:23.671347+00:00
-- url     : https://prove2.me/submissions/188dfb42-aa7b-422a-bf85-f2290273286a

import Mathlib
import Definitions.Def_Applications_EML_EMLDifferentialEquations
open EMLDiffEq EMLDiffEq.EMLExpr in
theorem solution (F : EMLExpr) (hF : ∀ x, Regular F x)
    (y : ℝ → ℝ) (hy : ∀ x, HasDerivAt y (eval (D F) x * y x) x) :
    ∃ K : ℝ, ∀ x, y x = K * Real.exp (eval F x) := by
  -- the symbolic derivative is the true derivative on the regular locus
  have hder : ∀ (e : EMLExpr) (x : ℝ), Regular e x → HasDerivAt (eval e) (eval (D e) x) x := by
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
  have hFd : ∀ x, HasDerivAt (eval F) (eval (D F) x) x := fun x => hder F x (hF x)
  -- `y · e^{-F}` has zero derivative, hence is constant
  have hg : ∀ x, HasDerivAt (fun z => y z * Real.exp (-eval F z)) 0 x := by
    intro x
    have h1 := (hy x).mul ((hFd x).neg.exp)
    convert h1 using 1
    ring
  have hconst : ∀ x, y x * Real.exp (-eval F x) = y 0 * Real.exp (-eval F 0) := fun x =>
    is_const_of_deriv_eq_zero (fun z => (hg z).differentiableAt) (fun z => (hg z).deriv) x 0
  refine ⟨y 0 * Real.exp (-eval F 0), fun x => ?_⟩
  rw [← hconst x, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
