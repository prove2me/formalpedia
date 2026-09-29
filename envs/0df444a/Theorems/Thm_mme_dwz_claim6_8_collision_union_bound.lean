-- Prove2me | Theorems.Thm_mme_dwz_claim6_8_collision_union_bound
-- name    : mme_dwz_claim6_8_collision_union_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T10:35:24.799771+00:00
-- url     : https://prove2.me/theorems/1918cff8-17d7-41f4-b92c-5069741cb7f8
-- title:
--   DWZ Claim 6.8: finite collision union bound
-- statement:
--   Let Ω be a finite space of hash parameters and let A be a finite set of competing blocks. Mark some competitors as compatible. Suppose every bad parameter collides with at least one compatible competitor, and for each compatible competitor a the collision fiber has cardinality at most |Ω|/M, expressed without division as M·|{ω : a collides at ω}| ≤ |Ω|. Then M·|Bad| ≤ |Compatible|·|Ω|. This is the exact finite union-bound step in DWZ Claim 6.8. The theorem does not assume the desired 1/8 conclusion: the later source-specific obligations are to count compatible competitors, instantiate Lemma 3.11's 1/M collision fiber, and prove the modulus lower bound.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Claim 6.8 and its union-bound calculation (PDF p. 57 / printed p. 56), using Lemma 3.11.

import Mathlib
open BigOperators
set_option autoImplicit false

theorem mme_dwz_claim6_8_collision_union_bound
    {Ω A : Type}
    [Fintype Ω] [DecidableEq Ω] [DecidableEq A]
    (candidates : Finset A)
    (compatible : A → Prop) [DecidablePred compatible]
    (collides : A → Ω → Prop) [∀ a, DecidablePred (collides a)]
    (bad : Ω → Prop) [DecidablePred bad]
    (M : ℕ)
    (hbad : ∀ ω, bad ω →
      ∃ a ∈ candidates, compatible a ∧ collides a ω)
    (hcollision : ∀ a ∈ candidates, compatible a →
      M * (Finset.univ.filter (collides a)).card ≤ Fintype.card Ω) :
    M * (Finset.univ.filter bad).card ≤
      (candidates.filter compatible).card * Fintype.card Ω := by sorry
