-- Prove2me | Theorems.Thm_mme_finite_incidence_first_second_moment_identities
-- name    : mme_finite_incidence_first_second_moment_identities
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:19:55.05067+00:00
-- url     : https://prove2.me/theorems/43ca9bff-9de0-4833-886e-74f3c8abd8b6
-- title:
--   Exact first- and second-moment identities for a finite incidence relation
-- statement:
--   For a finite parameter set $U$, a finite object set $A$, and an incidence relation $P(ω,a)$, let $D(ω)$ be the number of objects incident to $ω$. Then exact double counting gives
--
--   $$
--   \sum_{ω\in U}D(ω)=\sum_{a\in A}|\{ω\in U:P(ω,a)\}|,
--   $$
--
--   and
--
--   $$
--   \sum_{ω\in U}D(ω)^2=\sum_{(a,b)\in A^2}|\{ω\in U:P(ω,a)\land P(ω,b)\}|.
--   $$
--
--   These identities convert single-event and pair-intersection fiber counts into the first and second moments used by finite Paley--Zygmund arguments, without introducing normalized probabilities or division.
-- source:
--   Elementary finite double counting; counting-measure form of the first- and second-moment method

import Mathlib

open BigOperators

set_option autoImplicit false

theorem mme_finite_incidence_first_second_moment_identities
    {Ω α : Type} [DecidableEq Ω] [DecidableEq α]
    (U : Finset Ω) (A : Finset α) (P : Ω → α → Prop)
    [DecidableRel P] :
    (∑ ω ∈ U, (A.filter (fun a => P ω a)).card) =
        ∑ a ∈ A, (U.filter (fun ω => P ω a)).card ∧
    (∑ ω ∈ U, (A.filter (fun a => P ω a)).card ^ 2) =
        ∑ p ∈ A.product A,
          (U.filter (fun ω => P ω p.1 ∧ P ω p.2)).card := by
  sorry
