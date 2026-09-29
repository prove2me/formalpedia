-- Prove2me | Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
-- name    : mme_fintype_constrained_prescribed_fiber_function_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:34:30.391851+00:00
-- url     : https://prove2.me/theorems/6490046e-1151-4edc-b084-cda68f498ba8
-- title:
--   A stratified prescribed histogram is counted by a product of multinomials
-- statement:
--   Let finite sets $alpha$ and $beta$ map to the same finite set of strata. Prescribe a multiplicity $k_b$ for each value $b$ of $beta$, with the total multiplicity over every stratum equal to the number of domain points in that stratum. Then the number of functions that remain over the fixed base map and have exactly those fibers is the product, over strata, of the corresponding multinomial coefficients.
--
--   This is the conditional or row-stratified multinomial count needed for Coppersmith--Winograd completion degrees: a fixed mode word supplies the strata, and a supported joint-profile table prescribes the fibers inside each grade stratum.
-- source:
--   Finite stratified multinomial counting; applied to the completion tables in equations (12)--(13) of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false

theorem mme_fintype_constrained_prescribed_fiber_function_card
    {α β ι : Type*}
    [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    [Fintype ι] [DecidableEq ι]
    (h : α → ι) (q : β → ι) (k : β → ℕ)
    (hsum : ∀ i,
      (∑ b : {b : β // q b = i}, k b.1) =
        Fintype.card {a : α // h a = i}) :
    Nat.card
        {g : α → β //
          (∀ a, q (g a) = h a) ∧
          ∀ b, Fintype.card {a // g a = b} = k b} =
      ∏ i,
        (Fintype.card {a : α // h a = i}).factorial /
          ∏ b : {b : β // q b = i}, (k b.1).factorial := by
  sorry
