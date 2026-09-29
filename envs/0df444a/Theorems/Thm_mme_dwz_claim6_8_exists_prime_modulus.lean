-- Prove2me | Theorems.Thm_mme_dwz_claim6_8_exists_prime_modulus
-- name    : mme_dwz_claim6_8_exists_prime_modulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T19:01:06.958948+00:00
-- url     : https://prove2.me/theorems/561bf7a7-8ad8-4185-aeef-b93fd87ef70b
-- title:
--   DWZ Claim 6.8: existence of a bounded odd prime modulus
-- statement:
--   Let $M_0\ge 2$ be a natural scale that dominates the largest bounded hash address, eight times the first asymmetric-hashing collision budget, and eight times the compatible-candidate budget used in DWZ Claim 6.8. Then there exists an odd prime $p$ such that
--
--   $$M_0<p\le 2M_0,$$
--
--   and the address and both eightfold budgets are bounded by $p$ (strictly for the address). This is the finite Bertrand-theorem handoff which supplies one prime field satisfying every numerical side condition of the two hashing calculations. It does not assert the source-specific budget formulas, collision fibers, or the one-eighth hole bound.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Step 3 and the setup and proof of Claim 6.8 (printed pp. 50 and 53-57, PDF pp. 51 and 54-58); https://arxiv.org/abs/2210.10173.

import Mathlib.NumberTheory.Bertrand

set_option autoImplicit false

theorem mme_dwz_claim6_8_exists_prime_modulus
    (levelSum firstCollisionBudget compatibleCandidateBudget M0 : ℕ)
    (hM0 : 2 ≤ M0)
    (hlevel : levelSum ≤ M0)
    (hfirst : 8 * firstCollisionBudget ≤ M0)
    (hcompatible : 8 * compatibleCandidateBudget ≤ M0) :
    ∃ p : ℕ,
      p.Prime ∧ Odd p ∧
      levelSum < p ∧
      8 * firstCollisionBudget ≤ p ∧
      8 * compatibleCandidateBudget ≤ p ∧
      M0 < p ∧ p ≤ 2 * M0 := by
  sorry
