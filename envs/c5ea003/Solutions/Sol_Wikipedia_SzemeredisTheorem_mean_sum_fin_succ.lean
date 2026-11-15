-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_sum_fin_succ
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:15:39.140106+00:00
-- url     : https://prove2.me/submissions/51ef8651-accf-44a8-bb84-5488ba394725

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
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
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

































theorem mean₂_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean₂ f = mean₂ (fun y x => f x y) := by
  exact Finset.expect_comm Finset.univ Finset.univ f

end Wikipedia.SzemeredisTheorem

end

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





















































/-- Translation does not change normalized averaging on a finite additive
group. -/
theorem mean_add_right
    {G : Type*} [Fintype G] [AddCommGroup G]
    (h : G → ℝ) (c : G) :
    mean (fun x => h (x + c)) = mean h := by
  unfold mean
  exact Fintype.expect_equiv (Equiv.addRight c)
    (fun x => h (x + c)) h (fun _ => rfl)











end Wikipedia.SzemeredisTheorem

end
/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- For a nonempty tuple, its coordinate sum is uniformly distributed on a
finite additive group. -/
theorem solution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (h : G → ℝ) :
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i)) = mean h := by
  calc
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i)) =
        mean (fun p : G × (Fin n → G) =>
          h (p.1 + ∑ i, p.2 i)) := by
      unfold mean
      apply Fintype.expect_equiv
        (Fin.insertNthEquiv (fun _ : Fin (n + 1) => G) 0).symm
      intro x
      congr 1
      rw [Fin.sum_univ_succ]
      rfl
    _ = mean₂ (fun a : G => fun y : Fin n → G =>
          h (a + ∑ i, y i)) := by
      simpa [mean, mean₂] using
        (Finset.expect_product (Finset.univ : Finset G)
          (Finset.univ : Finset (Fin n → G))
          (fun p : G × (Fin n → G) => h (p.1 + ∑ i, p.2 i)))
    _ = mean₂ (fun y : Fin n → G => fun a : G =>
          h (a + ∑ i, y i)) := mean₂_comm _
    _ = mean (fun _ : Fin n → G => mean h) := by
      apply congrArg mean
      funext y
      exact mean_add_right h (∑ i, y i)
    _ = mean h := mean_const _
