-- Prove2me | Theorems.Thm_mme_dwz_asymmetric_hash_behrend_retention_from_exact_fibers
-- name    : mme_dwz_asymmetric_hash_behrend_retention_from_exact_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:56:40.638587+00:00
-- url     : https://prove2.me/theorems/b01d4f37-739d-44d2-b881-be492fd2f75b
-- title:
--   Asymmetric affine hashing retains an isolated family with explicit Behrend loss
-- statement:
--   Let $T$ be a target edge family inside a finite ambient family $A$, with every target X- and Y-fiber of size at most $d$. Suppose an affine hash over a positive modulus $p\ge4d$ has exactly $p^{N+3}$ states, every edge survives in exactly $|S|p^{N+1}$ states, and every distinct X- or Y-colliding pair survives together in at most $|S|p^N$ states for every three-term-progression-free set $S\subseteq[0,p/2)$. Then there is a concrete lower-half Behrend set, one hash state, and an X/Y-isolated retained family $I\subseteq T$ satisfying $$|I|\ge\frac{|T|\,(p/2)\exp(-4\sqrt{\log(p/2)})}{2p^2}.$$ The theorem displays the complete Salem--Spencer loss needed in the finite-to-asymptotic retained-copy rate calculation.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Equation (21), Algorithm 2, and the Salem--Spencer hashing step; https://arxiv.org/abs/2210.10173

import Mathlib
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_dwz_asymmetric_hash_retention_from_exact_fibers

set_option autoImplicit false

theorem mme_dwz_asymmetric_hash_behrend_retention_from_exact_fibers
    {Ω Edge X Y : Type}
    [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (A T : Finset Edge) (x : Edge → X) (y : Edge → Y)
    (N p d : ℕ) (hp : 0 < p) (hmod : 4 * d ≤ p)
    (hx : ∀ a ∈ T, (A.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ T, (A.filter (fun b ↦ y b = y a)).card ≤ d)
    (hstateCard : Fintype.card Ω = p ^ (N + 3))
    (hhash : ∀ S : Finset ℕ,
      S ⊆ Finset.range (p / 2) →
      ThreeAPFree (S : Set ℕ) →
      ∃ E : Ω → Finset Edge,
        (∀ ω, E ω ⊆ A) ∧
        (∀ a ∈ T,
          (Finset.univ.filter (fun ω : Ω ↦ a ∈ E ω)).card =
            S.card * p ^ (N + 1)) ∧
        ∀ q ∈ (T.product A).filter (fun q ↦
            q.1 ≠ q.2 ∧ (x q.1 = x q.2 ∨ y q.1 = y q.2)),
          (Finset.univ.filter (fun ω : Ω ↦
            q.1 ∈ E ω ∧ q.2 ∈ E ω)).card ≤
              S.card * p ^ N) :
    ∃ S : Finset ℕ, ∃ E : Ω → Finset Edge, ∃ ω : Ω,
      ∃ I : Finset Edge,
        S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        I ⊆ T ∧
        I ⊆ E ω ∧
        (∀ e ∈ I, ∀ e' ∈ E ω,
          x e = x e' ∨ y e = y e' → e = e') ∧
        ((T.card : ℝ) *
            (((p / 2 : ℕ) : ℝ) *
              Real.exp (-4 * Real.sqrt
                (Real.log (((p / 2 : ℕ) : ℝ)))))) /
            (2 * (p : ℝ) ^ 2) ≤
          (I.card : ℝ) := by
  sorry
