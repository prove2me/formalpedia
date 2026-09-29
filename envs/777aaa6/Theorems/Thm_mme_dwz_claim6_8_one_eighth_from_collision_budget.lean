-- Prove2me | Theorems.Thm_mme_dwz_claim6_8_one_eighth_from_collision_budget
-- name    : mme_dwz_claim6_8_one_eighth_from_collision_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T11:07:36.43883+00:00
-- url     : https://prove2.me/theorems/5cd52382-0eed-42f4-a316-5a76ee89a3df
-- title:
--   DWZ Claim 6.8: a collision budget leaves seven eighths non-holes
-- statement:
--   Let $\Omega$ be a finite conditioned hash-parameter space and let $C$ be the finite set of compatible competing addresses. For each $a\in C$, suppose its collision fiber has density at most $1/M$ in the exact form $M|F_a|\le |\Omega|$. Assume every bad parameter belongs to some $F_a$, the modulus $M$ is positive, and $8|C|\le M$. Then
--
--   $$8\,|\{\omega\in\Omega:\omega\text{ is bad}\}|\le |\Omega|.$$
--
--   Equivalently, at most one eighth of the conditioned parameters are holes. This is the exact finite union-and-modulus step in DWZ Claim 6.8; the concrete affine fiber and compatible-address count enter as separate inputs.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Claim 6.8 (printed pp. 56-57 / PDF pp. 57-58).

import Mathlib
import Theorems.Thm_mme_dwz_claim6_8_collision_union_bound
set_option autoImplicit false

theorem mme_dwz_claim6_8_one_eighth_from_collision_budget
    {Ω A : Type}
    [Fintype Ω] [DecidableEq Ω] [DecidableEq A]
    (candidates : Finset A)
    (compatible : A → Prop) [DecidablePred compatible]
    (collides : A → Ω → Prop) [∀ a, DecidablePred (collides a)]
    (bad : Ω → Prop) [DecidablePred bad]
    (M : ℕ) (hM : 0 < M)
    (hbad : ∀ ω, bad ω →
      ∃ a ∈ candidates, compatible a ∧ collides a ω)
    (hcollision : ∀ a ∈ candidates, compatible a →
      M * (Finset.univ.filter (collides a)).card ≤ Fintype.card Ω)
    (hbudget : 8 * (candidates.filter compatible).card ≤ M) :
    8 * (Finset.univ.filter bad).card ≤ Fintype.card Ω := by sorry
