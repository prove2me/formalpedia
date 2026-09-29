-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_hash_retention_from_exact_fibers
-- name    : mme_dwz_asymmetric_hash_retention_from_exact_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T03:54:12.241383+00:00
-- url     : https://prove2.me/theorems/4788418f-4146-4e60-9e44-c0b7de30f9e5
-- title:
--   DWZ asymmetric hash: retained X/Y-induced family from exact fibers
-- statement:
--   Let A be a finite ambient edge family and T a finite target subfamily, with X- and Y-labels. For each finite hash state ω, let Eω be the surviving ambient bucket. Assume every target edge has X-star and Y-star degree at most d in A, and 4d ≤ p. Assume the hash has exactly p^(N+3) states; every target edge survives in exactly |B|p^(N+1) states; and every distinct target–ambient pair sharing X or Y survives together in at most |B|p^N states. Then some state contains a target subfamily I of cardinality at least |T||B|/(2p²) such that every member of I is isolated, relative to the entire surviving bucket, from all distinct edges sharing its X- or Y-label. This is the finite incidence-and-pruning retention step; it does not assert Z-isolation, construct the affine hash, or conclude a tensor value or matrix-multiplication exponent.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 3.10, especially Lemma 3.11 and the asymmetric-hashing retention estimate on printed pp. 24–27; Section 6.2, Equation (21), printed pp. 53–54.

import Mathlib
import Theorems.Thm_mme_finset_incidence_double_count
import Theorems.Thm_mme_finite_collision_budget_averaging_real

open BigOperators
set_option autoImplicit false

theorem mme_dwz_asymmetric_hash_retention_from_exact_fibers
    {Ω Edge X Y : Type}
    [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (A T : Finset Edge) (x : Edge → X) (y : Edge → Y)
    (E : Ω → Finset Edge)
    (N p B d : ℕ) (hp : 0 < p) (hmod : 4 * d ≤ p)
    (hE : ∀ ω, E ω ⊆ A)
    (hx : ∀ a ∈ T, (A.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ T, (A.filter (fun b ↦ y b = y a)).card ≤ d)
    (hstateCard : Fintype.card Ω = p ^ (N + 3))
    (hsingle : ∀ a ∈ T,
      (Finset.univ.filter (fun ω : Ω ↦ a ∈ E ω)).card =
        B * p ^ (N + 1))
    (hpair : ∀ q ∈ (T.product A).filter (fun q ↦
        q.1 ≠ q.2 ∧ (x q.1 = x q.2 ∨ y q.1 = y q.2)),
      (Finset.univ.filter (fun ω : Ω ↦
        q.1 ∈ E ω ∧ q.2 ∈ E ω)).card ≤
          B * p ^ N) :
    ∃ ω : Ω, ∃ I : Finset Edge,
      I ⊆ T ∧
      I ⊆ E ω ∧
      (∀ e ∈ I, ∀ e' ∈ E ω,
        x e = x e' ∨ y e = y e' → e = e') ∧
      ((T.card : ℝ) * (B : ℝ)) /
          (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by
  sorry
