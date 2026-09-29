-- Prove2me | Theorems.Thm_mme_dwz_finite_candidate_family_common_prime_with_exponential_cap
-- name    : mme_dwz_finite_candidate_family_common_prime_with_exponential_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:16:42.472305+00:00
-- url     : https://prove2.me/theorems/12eb074d-fbca-4e31-9380-18173ec1fbb1
-- title:
--   One common hashing prime with exact cardinal and exponential caps
-- statement:
--   Let $d$ be the first-hash collision degree and let a finite family of second-hash candidate sets have a common real bound $R$. Assume both $d$ and the ambient outer-word universe are at most $15^L$. Then there are a common candidate cap $Q$ and one odd prime $p$ satisfying every first- and second-hash budget, with
--
--   $$
--   Q\le |\mathrm{Outer}|\le15^L,
--   \qquad
--   p\le2\max\{4,8\max(d,Q)\}\le e^{16(L+1)}.
--   $$
--
--   The theorem also retains the pointwise candidate bounds and the rate estimate $p\le\max\{8,16\max(d,R)\}$. It packages the exact finite cardinal information needed to normalize the Behrend factor without replacing either collision cap by an unspecified asymptotic term.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023 / arXiv:2210.10173v5, Claim 6.8 and the common-modulus choice in Section 6.2, printed pp. 55--57; the displayed exponential normalization is an elementary consequence of the finite ambient word count.

import Theorems.Thm_mme_dwz_finite_candidate_family_common_prime_with_card_cap
import Theorems.Thm_mme_dwz_common_prime_le_exp_sixteen_length

set_option autoImplicit false

theorem mme_dwz_finite_candidate_family_common_prime_with_exponential_cap
    {Outer Block : Type}
    [Fintype Outer] [DecidableEq Outer] [Nonempty Outer]
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    (L d : ℕ) (R : ℝ)
    (candidates : Outer → Block → Finset Outer)
    (hd : d ≤ 15 ^ L)
    (hOuter : Fintype.card Outer ≤ 15 ^ L)
    (hR : ∀ retained small, ((candidates retained small).card : ℝ) ≤ R) :
    ∃ Q p : ℕ,
      (∀ retained small, (candidates retained small).card ≤ Q) ∧
      Q ≤ Fintype.card Outer ∧
      Q ≤ 15 ^ L ∧
      (Q : ℝ) ≤ R ∧
      p.Prime ∧ Odd p ∧
      4 < p ∧
      8 * d ≤ p ∧
      (∀ retained small, 8 * (candidates retained small).card ≤ p) ∧
      max 4 (8 * max d Q) < p ∧
      p ≤ 2 * max 4 (8 * max d Q) ∧
      (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) ∧
      (p : ℝ) ≤ Real.exp (16 * (((L + 1 : ℕ) : ℝ))) := by
  sorry
