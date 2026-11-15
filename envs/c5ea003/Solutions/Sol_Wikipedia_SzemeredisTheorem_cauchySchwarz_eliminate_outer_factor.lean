-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cauchySchwarz_eliminate_outer_factor
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T09:59:34.974943+00:00
-- url     : https://prove2.me/submissions/e124fea0-a2de-494e-909d-a302baf6503a

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Products of independent finite means

The product of normalized averages over independent finite variables is the
normalized average over their product space.  This is the finite-probability
Fubini identity used when expanding products of generalized convolutions.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A normalized mean over a product type is the corresponding iterated
normalized mean. -/
theorem mean_prod_type
    {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℝ) :
    mean (fun p : α × β => F p.1 p.2) = mean₂ F := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) F)





end Wikipedia.SzemeredisTheorem

end

section


/-!
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/

namespace Wikipedia.SzemeredisTheorem

/-- Global Cauchy--Schwarz for a normalized finite mean. -/
theorem mean_mul_sq_le_product
    {Ω : Type*} [Fintype Ω]
    (u v : Ω → ℝ) :
    mean (fun x => u x * v x) ^ 2 ≤
      mean (fun x => u x ^ 2) *
        mean (fun x => v x ^ 2) := by
  simpa [mean] using
    (Finset.expect_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset Ω) u v)

/-- The square of a normalized mean is the mean over two independent copies
of the variable. -/
theorem mean_sq_eq_mean_pair_mul
    {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    mean f ^ 2 =
      mean (fun p : Ω × Ω => f p.1 * f p.2) := by
  calc
    mean f ^ 2 = mean f * mean f := pow_two _
    _ = mean₂ (fun x y => f x * f y) := by
      unfold mean₂ mean
      exact
        Finset.expect_mul_expect
          Finset.univ Finset.univ f f
    _ = mean (fun p : Ω × Ω => f p.1 * f p.2) :=
      (mean_prod_type fun x y => f x * f y).symm

/-- Squaring an inner mean duplicates its variable under the outer mean. -/
theorem mean_inner_sq_eq_mean₂_pair
    {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → ℝ) :
    mean (fun x => mean (F x) ^ 2) =
      mean₂ (fun x => fun p : Y × Y =>
        F x p.1 * F x p.2) := by
  unfold mean₂
  apply congrArg mean
  funext x
  exact mean_sq_eq_mean_pair_mul (F x)











end Wikipedia.SzemeredisTheorem

end
/-!
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
/-- One normalized Cauchy--Schwarz elimination step.  The factor `u`,
which is independent of the inner variable, disappears; the inner variable
is replaced by two independent copies. -/
theorem solution
    {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y]
    (u : X → ℝ) (F : X → Y → ℝ)
    (hu : ∀ x, |u x| ≤ 1) :
    mean₂ (fun x y => u x * F x y) ^ 2 ≤
      mean₂ (fun x => fun p : Y × Y =>
        F x p.1 * F x p.2) := by
  have hrewrite :
      mean₂ (fun x y => u x * F x y) =
        mean (fun x => u x * mean (F x)) := by
    unfold mean₂
    apply congrArg mean
    funext x
    exact mean_smul (u x) (F x)
  rw [hrewrite]
  calc
    mean (fun x => u x * mean (F x)) ^ 2 ≤
        mean (fun x => u x ^ 2) *
          mean (fun x => mean (F x) ^ 2) :=
      mean_mul_sq_le_product u (fun x => mean (F x))
    _ ≤ mean (fun x => mean (F x) ^ 2) := by
      have huSq : mean (fun x => u x ^ 2) ≤ 1 := by
        apply mean_le_of_le_const
        intro x
        have hx := abs_le.mp (hu x)
        nlinarith [sq_nonneg (u x - 1), sq_nonneg (u x + 1)]
      have hmeanSq :
          0 ≤ mean (fun x => mean (F x) ^ 2) :=
        mean_nonneg fun x => sq_nonneg _
      exact mul_le_of_le_one_left hmeanSq huSq
    _ = mean₂ (fun x => fun p : Y × Y =>
          F x p.1 * F x p.2) :=
      mean_inner_sq_eq_mean₂_pair F
