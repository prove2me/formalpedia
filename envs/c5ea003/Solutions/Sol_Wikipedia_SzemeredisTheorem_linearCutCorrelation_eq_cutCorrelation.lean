-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.linearCutCorrelation_eq_cutCorrelation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:01.293197+00:00
-- url     : https://prove2.me/submissions/ef8875fc-1bb5-41c4-90bf-9d8d363c14a6

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl





























































end Wikipedia.SzemeredisTheorem

end

section


/-!
# Transport of cut discrepancy by coordinate automorphisms

Arithmetic-progression face forms are weighted coordinate sums rather than
literal sums.  When every coefficient acts by an additive automorphism, a
coordinatewise change of variables reduces them to the literal sum used in
`CutDiscrepancyLe`.  This file proves that reduction once and for all.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators







@[simp]
theorem coordinatewiseAddEquiv_apply
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G)
    (x : ι → G) (i : ι) :
    coordinatewiseAddEquiv e x i = e i (x i) :=
  rfl













end Wikipedia.SzemeredisTheorem

end
/-!
# Transport of cut discrepancy by coordinate automorphisms

Arithmetic-progression face forms are weighted coordinate sums rather than
literal sums.  When every coefficient acts by an additive automorphism, a
coordinatewise change of variables reduces them to the literal sum used in
`CutDiscrepancyLe`.  This file proves that reduction once and for all.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Coordinatewise automorphisms turn a weighted-sum correlation into an
ordinary sum correlation with pulled-back tests. -/
theorem solution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (e : Fin r → G ≃+ G)
    (f g : G → ℝ) (u : CutTestFamily G r) :
    linearCutCorrelation r e f g u =
      cutCorrelation r f g (pullCutTest e u) := by
  cases r with
  | zero =>
      simp [linearCutCorrelation, cutCorrelation, pullCutTest]
  | succ n =>
      unfold linearCutCorrelation cutCorrelation mean
      apply Fintype.expect_equiv (coordinatewiseAddEquiv e)
      intro x
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      change
        u i (eraseCoordinate i x) =
          u i (fun t =>
            (e (i.succAbove t)).symm
              (eraseCoordinate i
                (coordinatewiseAddEquiv e x) t))
      congr 1
      funext t
      simp
