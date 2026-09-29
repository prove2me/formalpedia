-- Prove2me | Theorems.Thm_mme_dwz_q6_assemble_one_half_pointwise
-- name    : mme_dwz_q6_assemble_one_half_pointwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T13:09:42.827451+00:00
-- url     : https://prove2.me/theorems/5c137250-f174-4774-9306-7be55804baeb
-- title:
--   Pointwise one-half primary capacity yields the doubled six-symmetric rate
-- statement:
--   Fix a primary-hash scale N and parameters L, G, A, H. Suppose a tensor contains an outer family of A C-tensor stars with H ≤ 4^N inner components and common volume 6^(4G+2L). If the primary-capacity lower bound at source loss exp(-C₀√(N+1)) holds, then the tensor's six-symmetrization has a finite matrix-multiplication extraction of total τ-weight at least
--
--   $$(4 · 6^{3τ}(6^{3τ}+2))^{4N} · exp(-(2C₀+400)√(N+1)).$$
--
--   This is the pointwise quantitative assembly after completing one cyclic C-tensor extraction and tensoring it with its mode-swapped copy.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Lemma 4.6(d) and the Table-2 coupled-component rate calculation; post-cyclic doubling uses tensor restriction functoriality.

import Mathlib
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_six_symmetrized_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_dwz_q6_assemble_one_half_pointwise
    {K : Type u} [Field K]
    (tau C₀ : ℝ) (N L G A H : ℕ) (T : TensorObj K 3)
    (stars : CTensorOneHOneFamilyCertificate
      T A H (6 ^ (4 * G + 2 * L)))
    (hHbound : H ≤ 4 ^ N)
    (hrate :
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (2 * N) *
          Real.exp (-C₀ * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          (((((36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) *
            (36 ^ (2 * G) * 6 ^ (2 * L)) : ℕ) : ℝ)) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization T) ∧
      (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^
            (4 * N) *
          Real.exp (-(2 * C₀ + 400) *
            Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  sorry
