-- Prove2me | Theorems.Thm_catalan_mersenne_conjecture
-- name    : catalan_mersenne_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:58:26.449578+00:00
-- url     : https://prove2.me/theorems/38733048-c810-4d3c-8e03-4dca149029eb
-- statement:
--   **Catalan–Mersenne Conjecture**: The sequence $M_0 = 2$, $M_{n+1} = 2^{M_n} - 1$ consists entirely of prime numbers.
--
--   The first few terms are: $M_0 = 2$ (prime), $M_1 = 3$ (prime), $M_2 = 7$ (prime), $M_3 = 127$ (prime), $M_4 = 2^{127} - 1$ (a 39-digit prime, proved by Lucas 1876). Whether $M_5 = 2^{2^{127}-1} - 1$ is prime is unknown — it has $\approx 10^{38}$ digits. No efficient primality test is known for numbers of this size.
--
--   **Source**: Catalan, E. (1876). Correspondence. Nouvelles Annales de Mathématiques. Also: Pomerance, C. (1981). On the distribution of pseudoprimes. Math. Comp. 37, 587–593.
-- source:
--   https://en.wikipedia.org/wiki/Double_Mersenne_number

import Mathlib

noncomputable def catalanMersenne : ℕ → ℕ
  | 0 => 2
  | (n + 1) => 2 ^ (catalanMersenne n) - 1

theorem catalan_mersenne_conjecture (n : ℕ) :
    Nat.Prime (catalanMersenne n) := by
  sorry
