-- Prove2me | Theorems.Thm_ZetaNine_HarmonicStability_harmonic_finite_prime_product_dvd
-- name    : ZetaNine.HarmonicStability.harmonic_finite_prime_product_dvd
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:50:09.3879+00:00
-- url     : https://prove2.me/theorems/88f03ef4-6450-42cd-97d3-24e924ee4e1c
-- title:
--   Finite admitted prime powers divide the actual harmonic denominator
-- statement:
--   Let $s>0$, $K,N\ge0$, and let $S$ be a finite set of primes. Put $H_N^{(s)}=\sum_{j=1}^{N}j^{-s}$ and
--
--   $$E_{s,K}=\prod_{k=1}^{K}\left|\operatorname{num}(H_k^{(s)})\right|.$$
--
--   Suppose every $p\in S$ satisfies
--
--   $$p\le N,\qquad \lfloor N/p\rfloor\le K,\qquad K<p,\qquad E_{s,K}<p.$$
--
--   Then the full finite prime-power product divides the reduced positive harmonic denominator:
--
--   $$\prod_{p\in S}p^s\mid\operatorname{den}(H_N^{(s)}).$$
--
--   All hypotheses refer to the actual finite harmonic prefixes. The explicit exception bound is a sufficient way to exclude their numerator prime factors; it is not a claim that every large prime is automatically a unit. The theorem supplies finite arithmetic and does not assert any asymptotic prime count or denominator growth rate.
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

theorem ZetaNine.HarmonicStability.harmonic_finite_prime_product_dvd (s K N : ℕ) (S : Finset ℕ)
    (hs : 0 < s)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ N / p ≤ K ∧ K < p ∧
      harmonicExceptionalProduct s K < p) :
    (∏ p ∈ S, p ^ s) ∣ (harmonicPower s N).den := by sorry
