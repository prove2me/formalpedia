-- Prove2me | Theorems.Thm_ZetaNine_finite_prime_discount
-- name    : ZetaNine.finite_prime_discount
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-24T15:26:13.139885+00:00
-- url     : https://prove2.me/theorems/0f7bb5e3-be14-422d-a555-d89ed96e171f
-- title:
--   Exact finite weighted prime-discount identity
-- statement:
--   For any finite index set, natural-number values v and a, and arbitrary real weights w, the weighted sum of the truncated exponents (v−2a) plus the weighted sum of min((11a−v),9a) equals nine times the weighted sum of a plus the weighted sum of (v−11a). All natural-number subtractions are truncated at zero. This is the exact finite algebraic identity behind the local ζ(9) prime-discount formula; the theorem does not define its concrete Smith modulus, prime valuations, or asymptotic limit.
-- source:
--   Local zeta9 research note, roadmap/research/prime-discount-identity.md, equations (2)-(3), 2026-09-24

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace ZetaNine

theorem finite_prime_discount
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v a : ι → ℕ) (w : ι → ℝ) :
    (∑ i ∈ s, ((v i - 2 * a i : ℕ) : ℝ) * w i) +
      (∑ i ∈ s, ((min (11 * a i - v i) (9 * a i) : ℕ) : ℝ) * w i) =
      9 * ∑ i ∈ s, (a i : ℝ) * w i +
        ∑ i ∈ s, ((v i - 11 * a i : ℕ) : ℝ) * w i := by sorry

end ZetaNine
