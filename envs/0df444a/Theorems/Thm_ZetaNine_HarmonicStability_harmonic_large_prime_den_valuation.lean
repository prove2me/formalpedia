-- Prove2me | Theorems.Thm_ZetaNine_HarmonicStability_harmonic_large_prime_den_valuation
-- name    : ZetaNine.HarmonicStability.harmonic_large_prime_den_valuation
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:50:26.988809+00:00
-- url     : https://prove2.me/theorems/e154a4ca-96a1-4257-b8a1-3a83e98f4111
-- title:
--   A unit harmonic prefix forces the exact large-prime denominator exponent
-- statement:
--   Let $s>0$ and $N\ge0$, and let $p$ be prime with $p\le N<p^2$. If $p$ does not divide the reduced numerator of the actual prefix $H_{\lfloor N/p\rfloor}^{(s)}$, then
--
--   $$v_p\!\left(\operatorname{den}(H_N^{(s)})\right)=s,\qquad H_N^{(s)}=\sum_{j=1}^{N}j^{-s}.$$
--
--   The numerator-unit condition is essential. For example, $H_2^{(9)}=513/512$ has a factor $19$ in its numerator, and for $N=38,p=19$ the actual denominator exponent is eight instead of nine. The theorem concerns the exact reduced positive denominator for each admitted parameter; it does not invoke the prime number theorem.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/harmonic-denominator-stability-2026-10-01.md, sections 1–2, equations (1)–(2) and the finite-prime lower-bound argument preceding equation (3).

import Definitions.Def_ZetaNine_HarmonicStability
import Definitions.Def_ZetaNine_HarmonicPrimeValuation
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic
open scoped BigOperators
open ZetaNine.HarmonicStability

theorem ZetaNine.HarmonicStability.harmonic_large_prime_den_valuation (s N p : ℕ) (hp : p.Prime)
    (hs : 0 < s) (hNp : p ≤ N) (hN : N < p ^ 2)
    (hunit : ¬ p ∣ (harmonicPower s (N / p)).num.natAbs) :
    padicValNat p (harmonicPower s N).den = s := by sorry
