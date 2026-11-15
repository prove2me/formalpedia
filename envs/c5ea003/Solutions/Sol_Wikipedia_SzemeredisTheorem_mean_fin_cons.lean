-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_fin_cons
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:56.633977+00:00
-- url     : https://prove2.me/submissions/3b3703b4-d8d1-4461-9e1f-74d6f6b87830

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
/-!
# Products of independent finite means

The product of normalized averages over independent finite variables is the
normalized average over their product space.  This is the finite-probability
Fubini identity used when expanding products of generalized convolutions.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Split the normalized mean over an `(n + 1)`-tuple into the head
coordinate and the remaining `n` coordinates. -/
theorem solution
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ) :
    mean F =
      mean₂ (fun a : G => fun y : Fin n → G => F (Fin.cons a y)) := by
  calc
    mean F =
        mean (fun p : G × (Fin n → G) =>
          F (Fin.cons p.1 p.2)) := by
      unfold mean
      apply Fintype.expect_equiv
        (Fin.consEquiv (fun _ : Fin (n + 1) => G)).symm
      intro x
      congr 1
      simp
    _ = mean₂ (fun a : G => fun y : Fin n → G =>
          F (Fin.cons a y)) :=
      mean_prod_type
        (fun a : G => fun y : Fin n → G => F (Fin.cons a y))
