-- Prove2me | Theorems.Thm_Zeta9Note_taylor_sign_implies_kernel_sum_pos
-- name    : Zeta9Note.taylor_sign_implies_kernel_sum_pos
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T07:31:44.360455+00:00
-- url     : https://prove2.me/theorems/6b04ab7c-c253-4c74-ae6d-9f7298bdd7c2
-- title:
--   Nonnegative Taylor coefficients force a positive weighted kernel sum
-- statement:
--   Let R be a strictly positive sequence, u a sequence bounded below by u₀, and p a polynomial whose Taylor expansion at u₀ has nonnegative coefficients. If the weighted sample sum Σ' R_k p(u_k) is summable and at least one sample value p(u_k) is positive, then that sum is strictly positive.
-- source:
--   Abstract layer distilled from the v0.1 research note (Zenodo 10.5281/zenodo.22951155); statement and proof in formalization/Zeta9Note.lean.

import Mathlib

namespace Zeta9Note

theorem taylor_sign_implies_kernel_sum_pos
    (R u : ℕ → ℝ) (p : Polynomial ℝ) (u₀ : ℝ)
    (hR : ∀ k : ℕ, 0 < R k)
    (hu : ∀ k : ℕ, u₀ ≤ u k)
    (hcoeff : ∀ i : ℕ, 0 ≤ (Polynomial.taylor u₀ p).coeff i)
    (hsummable : Summable (fun k : ℕ => R k * p.eval (u k)))
    (hnonzero : ∃ k : ℕ, 0 < p.eval (u k)) :
    0 < ∑' k : ℕ, R k * p.eval (u k) := by sorry

end Zeta9Note
