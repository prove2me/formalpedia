-- Prove2me | solution 1 for mme_fintype_constrained_prescribed_fiber_function_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T11:19:19.617094+00:00
-- url     : https://prove2.me/submissions/63dc9c66-9047-490e-b2a1-ceec67571d09

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Mathlib.Data.Nat.Choose.Multinomial

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {alpha beta iota : Type*}
    [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    [Fintype iota] [DecidableEq iota]
    (h : alpha → iota) (q : beta → iota) (k : beta → ℕ)
    (hsum : ∀ i,
      (∑ b : {b : beta // q b = i}, k b.1) =
        Fintype.card {a : alpha // h a = i}) :
    Nonempty
      {g : alpha → beta //
        (∀ a, q (g a) = h a) ∧
        ∀ b, Fintype.card {a // g a = b} = k b} := by
  have hcard :=
    mme_fintype_constrained_prescribed_fiber_function_card h q k hsum
  have hPositive :
      0 < ∏ i,
        (Fintype.card {a : alpha // h a = i}).factorial /
          ∏ b : {b : beta // q b = i}, (k b.1).factorial := by
    apply Finset.prod_pos
    intro i hi
    rw [show
      (Fintype.card {a : alpha // h a = i}).factorial /
          ∏ b : {b : beta // q b = i}, (k b.1).factorial =
        Nat.multinomial Finset.univ (fun b : {b : beta // q b = i} ↦ k b.1) by
      rw [Nat.multinomial, hsum i]]
    exact Nat.multinomial_pos Finset.univ _
  have hNatCard :
      0 < Nat.card
        {g : alpha → beta //
          (∀ a, q (g a) = h a) ∧
          ∀ b, Fintype.card {a // g a = b} = k b} := by
    rw [hcard]
    exact hPositive
  exact (Nat.card_pos_iff.mp hNatCard).1
