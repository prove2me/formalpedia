-- Prove2me | Theorems.Thm_mme_primary_hash_uniform_stars_joint_directional_capacity
-- name    : mme_primary_hash_uniform_stars_joint_directional_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:31:06.673244+00:00
-- url     : https://prove2.me/theorems/cc4487e0-01c9-4d2c-b972-d85620066096
-- title:
--   Uniform shared stars jointly retain central-binomial X/Y capacity
-- statement:
--   For any natural lengths L+G=N and retained star/component counts A,H, suppose the two exact finite lower bounds supplied by uniform-star hashing hold with loss exp(-C sqrt(N+1)). The product of the ambient Z multinomial count and the middle central-binomial count equals choose(2N,N) times choose(N,G)^2. Consequently the same family jointly satisfies choose(2N,N) exp(-2C sqrt(N+1)) <= 4 A H, while preserving its separate Z-direction bound. This is a finite directional capacity statement, not an entropy-limit or tensor-value assertion.
-- source:
--   Finite consequence of the uniform-stars square-root-loss theorem mme_CW_q6_primary_hash_uniform_stars_sqrt_loss (Prove2Me ff1bc517; q-independent family), supporting the enhanced112 construction of Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/abs/2210.10173v5, Section6.3. Consumer: Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, released src/evaluation/TermInfoLv2.m (directional counts) and Workspace.m (sums before minima). The binomial identity follows exactly from Mathlib Nat.choose_mul and Nat.choose_symm_of_eq_add.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem mme_primary_hash_uniform_stars_joint_directional_capacity
    (N L G A H : ℕ) (hLG : L + G = N) (C : ℝ)
    (hA : ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
      Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ))
    (hH : (Nat.choose (2 * G) G : ℝ) *
      Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
      4 * (Nat.choose N G : ℝ) ^ 2 * (H : ℝ)) :
    ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
        Nat.choose (2 * G) G =
      Nat.choose (2 * N) N * (Nat.choose N G) ^ 2) ∧
    (((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
      Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ)) ∧
    ((Nat.choose (2 * N) N : ℝ) *
      Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
      4 * (A : ℝ) * (H : ℝ)) := by sorry
