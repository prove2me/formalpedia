-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cfzCoefficientEval_eq_apLinearForm
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:07:41.037378+00:00
-- url     : https://prove2.me/submissions/d45c8ce6-9728-4708-a51c-42bbb7e51850

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Independence of the Conlon--Fox--Zhao forms

The Goldston--Yıldırım linear-forms estimate requires the coefficient vectors
of distinct forms to be nonzero and pairwise non-proportional.  This file
records those facts over `ℤ` for the concrete CFZ family.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
/-- The coefficient-vector presentation evaluates to the original
`apLinearForm`. -/
theorem solution (k N : ℕ)
    (q : CFZFormIndex k) (x : CubePoint k N) :
    cfzCoefficientEval k N q x =
      apLinearForm k N q.1 q.2 x := by
  rcases q with ⟨j, ω⟩
  classical
  rw [cfzCoefficientEval, Fintype.sum_prod_type]
  let g : Fin k → ZMod N := fun i =>
    ∑ b : Bool,
      (cfzCoefficient ⟨j, ω⟩ (i, b) : ZMod N) * x i b
  change (∑ i, g i) = _
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin k => i ≠ j) g]
  have hnot : (∑ i : {i : Fin k // ¬ i ≠ j}, g i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : i.1 = j := not_ne_iff.mp i.2
    simp [g, cfzCoefficient, hi]
  rw [hnot, add_zero]
  apply Fintype.sum_congr
  intro i
  cases hω : ω i <;>
    simp [g, cfzCoefficient, i.2, hω]
