-- Prove2me | Theorems.Thm_mme_finset_incidence_double_count
-- name    : mme_finset_incidence_double_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:08:27.851308+00:00
-- url     : https://prove2.me/theorems/717357bf-c953-410b-8bc0-79bfb630f24c
-- title:
--   A finite incidence relation can be counted through either projection
-- statement:
--   For finite sets $W$ and $U$ and any incidence relation $P$ between them, the total number of incidences obtained by summing the $U$-fiber sizes over $W$ equals the total obtained by summing the $W$-fiber sizes over $U$. In symbols, summing $|{a in U : P(omega,a)}|$ over $omega in W$ equals summing $|{omega in W : P(omega,a)}|$ over $a in U$.
--
--   This is the finite double-counting identity used to convert per-edge affine-hash survival probabilities into aggregate retained-edge and collision counts.
-- source:
--   Elementary finite double counting; used in the affine outer-hash incidence argument of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib

open BigOperators

set_option autoImplicit false

theorem mme_finset_incidence_double_count
    {Ω A : Type} [DecidableEq Ω] [DecidableEq A]
    (W : Finset Ω) (U : Finset A) (P : Ω → A → Prop)
    [DecidableRel P] :
    (∑ ω ∈ W, (U.filter (P ω)).card) =
      ∑ a ∈ U, (W.filter (fun ω => P ω a)).card := by
  sorry
