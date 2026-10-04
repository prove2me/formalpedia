-- Prove2me | Theorems.Thm_ZetaNine_HarmonicStability_harmonic_finite_prime_log_lower_bound
-- name    : ZetaNine.HarmonicStability.harmonic_finite_prime_log_lower_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:50:24.436977+00:00
-- url     : https://prove2.me/theorems/d1e6ecea-242f-412b-b0b2-fc517132c9b3
-- title:
--   Finite prime logarithms bound the actual harmonic log denominator below
-- statement:
--   Let $s>0$, $K,N\ge0$, and let $S$ be a finite set of primes. With $H_N^{(s)}=\sum_{j=1}^{N}j^{-s}$ and $E_{s,K}=\prod_{k=1}^{K}|\operatorname{num}(H_k^{(s)})|$, suppose every $p\in S$ satisfies
--
--   $$p\le N,\qquad \lfloor N/p\rfloor\le K,\qquad K<p,\qquad E_{s,K}<p.$$
--
--   Then
--
--   $$s\sum_{p\in S}\log p\le\log\operatorname{den}(H_N^{(s)}).$$
--
--   Here the denominator is fully reduced and positive. The finite inequality holds for every admitted finite prime set, including the empty set. It is the arithmetic lower bound before applying the prime number theorem; no asymptotic prime-distribution or full-sequence denominator-rate statement is part of the conclusion.
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

theorem ZetaNine.HarmonicStability.harmonic_finite_prime_log_lower_bound (s K N : ℕ) (S : Finset ℕ)
    (hs : 0 < s)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ N / p ≤ K ∧ K < p ∧
      harmonicExceptionalProduct s K < p) :
    (s : ℝ) * (∑ p ∈ S, Real.log (p : ℝ)) ≤ logDen (harmonicPower s N) := by sorry
