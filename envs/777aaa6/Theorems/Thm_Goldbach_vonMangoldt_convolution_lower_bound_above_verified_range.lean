-- Prove2me | Theorems.Thm_Goldbach_vonMangoldt_convolution_lower_bound_above_verified_range
-- name    : Goldbach.vonMangoldt_convolution_lower_bound_above_verified_range
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T17:48:50.856564+00:00
-- url     : https://prove2.me/theorems/592b1426-d8d6-4548-9b5f-47a15ea9d536
-- title:
--   Uniform binary von Mangoldt lower bound above the verified Goldbach range
-- statement:
--   Let $\Lambda$ be the von Mangoldt function. For every even natural number $N>4\cdot10^{18}$, the proposed quantitative binary-correlation obligation is
--
--   $$\sum_{m=0}^{N}\Lambda(m)\Lambda(N-m)>2\lfloor\sqrt N\rfloor\lfloor\log_2N\rfloor(\log N)^2.$$
--
--   This is an unproved sufficient analytic condition for the strong Goldbach mission, not an established estimate. The right-hand side bounds the contamination by pairs containing proper prime powers, so this strict estimate forces an actual prime pair. Together with the separately registered finite verification up to $4\cdot10^{18}$, it would imply the original conjecture. Its uniform quantifier is essential: an average estimate or a bound outside an exceptional set does not establish this obligation.
-- source:
--   Sufficient quantitative research obligation for https://prove2.me/missions/The_Goldbach_Conjecture, applying Goldbach.vonMangoldt_convolution_extract_prime_pair, https://prove2.me/theorems/83119b08-dc6a-47ea-b6ae-f7063d47a82f. This is proposed proof architecture, not a claimed literature theorem.

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Sqrt
open scoped BigOperators
set_option autoImplicit false

theorem Goldbach.vonMangoldt_convolution_lower_bound_above_verified_range
    (N : ℕ) (hN : 4*10^18 < N) (he : Even N) :
    2 * (Nat.sqrt N * Nat.log 2 N : ℕ) * (Real.log N)^2 <
      ∑ m ∈ Finset.range (N+1),
        ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt (N-m) := by sorry
