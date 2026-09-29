-- Prove2me | Theorems.Thm_mme_CW_primary_profile_capacity_quarter_root
-- name    : mme_CW_primary_profile_capacity_quarter_root
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T14:47:39.449537+00:00
-- url     : https://prove2.me/theorems/fb9b5d5e-512a-4ed6-a797-e58cee4ba310
-- title:
--   Multinomial capacity of the coupled floor profile at every q
-- statement:
--   The multinomial capacity of the coupled floor profile dominates the raw laser base, for every $q\ge3$.
--
--   With $\lambda=2/(q^{3\tau}+2)$, $L=\lfloor\lambda N\rfloor$, $G=N-L$, write
--   $$Z=\binom{2N}{L}\binom{2N-L}{L},\qquad X=\binom{N}{G},\qquad B=\binom{2G}{G},\qquad \text{capacity}=\frac{Z^3B^2}{16X^4},$$
--   $$\text{side}=q^{4G+2L},\qquad \text{raw}=4q^{3\tau}\bigl(q^{3\tau}+2\bigr),\qquad \text{loss}=(N+1)^{-1/4}.$$
--   Then, eventually in $N$ and whenever $L>0$, $G>0$, $L+G=N$,
--   $$\bigl(\text{raw}\cdot e^{-\text{loss}/2}\bigr)^{2N}\;\le\;\bigl(\text{capacity}\cdot e^{-N\,\text{loss}/2}\bigr)\cdot\bigl(\text{side}^3\bigr)^{\tau}.$$
--
--   **What is actually being proved.** At the level of exponential rates the two sides *agree exactly*: writing $x=q^{3\tau}$ and $\lambda=2/(x+2)$, the identity
--   $$3\Bigl[2H\bigl(\tfrac\lambda2\bigr)+(2-\lambda)H\bigl(\tfrac{\lambda}{2-\lambda}\bigr)\Bigr]-4H(\lambda)+4(1-\lambda)\log 2+(4-2\lambda)\log x \;=\; 2\log\bigl(4x(x+2)\bigr)$$
--   holds for every $x>0$ — $\lambda=2/(x+2)$ is precisely the maximiser. So there is no slack to exploit, and the whole content of the statement is that the Stirling polynomial corrections and the cost of rounding $\lambda N$ down to an integer are absorbed by the quarter-root loss $e^{-N^{3/4}/2}$, which decays faster than any polynomial but slower than any exponential.
--
--   This is the general-$q$ form of `mme_CW_q6_primary_profile_capacity_quarter_root`; the hypothesis is weakened from the full pruning triple to $L>0\wedge G>0\wedge L+G=N$, since the ratio condition $341L<100G$ is not used here.
-- source:
--   Don Coppersmith and Shmuel Winograd, Matrix multiplication via arithmetic progressions, Journal of Symbolic Computation 9(3), 1990, 251-280; the coupled four-sum constituent (d) on printed p. 266 and its value lemma on printed p. 270. General-q form of the q=6 chain used for omega < 2.376.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
open Filter Topology

theorem mme_CW_primary_profile_capacity_quarter_root
    (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((q : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let side : ℕ := q ^ (4 * Gcount + 2 * L)
      let raw : ℝ :=
        4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2)
      let Zcount : ℕ :=
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      let Xcount : ℕ := Nat.choose N Gcount
      let middle : ℕ := Nat.choose (2 * Gcount) Gcount
      let capacity : ℝ :=
        ((Zcount : ℝ) ^ 3 * (middle : ℝ) ^ 2) /
          (16 * (Xcount : ℝ) ^ 4)
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ 0 < Gcount ∧ L + Gcount = N) →
        (raw * Real.exp (-(loss / 2))) ^ (2 * N) ≤
          (capacity * Real.exp (-((N : ℝ) * loss / 2))) *
            ((((side * side * side : ℕ) : ℝ)) ^ tau) := by
  sorry
