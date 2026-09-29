-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_sqrt_capacity
-- name    : mme_CW_q6_primary_hash_sqrt_capacity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:18:29.942745+00:00
-- url     : https://prove2.me/theorems/a908bd74-78a5-48ad-8a20-5b4b8add5b4e
-- title:
--   Coupled q=6 primary hash: finite capacity with square-root loss
-- statement:
--   Let $\tau\ge2/3$ and put $\lambda=2/(6^{3\tau}+2)$. For all sufficiently large powers $2N$, choose the exact integer profile $L=\lfloor\lambda N\rfloor$ and $G=N-L$. Then there are primary asymmetric-hash parameters $A,H$ and an induced hash family with those marginals such that
--
--   $$
--   \left(4\,6^{3\tau}(6^{3\tau}+2)\right)^{2N}e^{-C\sqrt{N+1}}\le A^3H^2\left((36^{2G}6^{2L})^3\right)^{\tau}.
--   $$
--
--   The theorem is a purely finite counting-and-rate certificate. It combines the exact floor profile, multinomial capacity, induced primary-family counts, and absorption of all polynomial factors into a square-root exponential loss; it contains no tensor-source identification.
-- source:
--   Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, J. Symbolic Computation 9 (1990), coupled constituent analysis on journal pp. 266-271; specialized to q=6 and used in Duan--Wu--Zhou, arXiv:2210.10173v5, Section 6.3.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME BigOperators Filter

set_option autoImplicit false

theorem mme_CW_q6_primary_hash_sqrt_capacity
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
        let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
        let G : ℕ := N - L
        let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
        let raw : ℝ :=
          4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
        ∃ A H : ℕ,
          ∃ family : CWQ6PrimaryHashFamily N L G A H,
            raw ^ (2 * N) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
                ((((side * side * side : ℕ) : ℝ)) ^ tau) := by sorry
