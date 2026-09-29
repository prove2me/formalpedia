-- Prove2me | Theorems.Thm_dedekindSum_of_mul_modEq_one
-- name    : dedekindSum_of_mul_modEq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/9307175b-2cf3-54c1-8201-c3cb69e2a989
-- title:
--   Invariance of s(h,k) under inversion modulo k
-- statement:
--   Let $h$, $h'$ and $k$ be natural numbers such that $h h' \equiv 1 \pmod{k}$. Here, for an integer $a$ and a natural number $m$, the Dedekind sum is defined by $$s(a,m) = \sum_{r=0}^{m-1} \big(\!\!\big(\tfrac{r}{m}\big)\!\!\big)\,\big(\!\!\big(\tfrac{a r}{m}\big)\!\!\big),$$ a rational number, where the sawtooth function is given on a rational $x$ by $((x)) = 0$ if the fractional part of $x$ vanishes and $((x)) = \{x\} - \tfrac12$ otherwise, with $\{x\}$ the fractional part; for $m = 0$ the sum is empty, hence $0$. The conclusion is the equality of rationals $s(h',k) = s(h,k)$, the arguments $h$ and $h'$ being taken as integers via the canonical map from $\mathbb{N}$. Thus the Dedekind sum is unchanged when the first argument is replaced by an inverse of it modulo the second; no positivity, coprimality or size hypotheses beyond the stated congruence are imposed.
--
--   This is the classical invariance $s(h',k) = s(h,k)$ for $h h' \equiv 1 \pmod k$, one of the elementary arithmetic properties of Dedekind sums alongside periodicity in $h$ and the reciprocity law. It is used in the evaluation of a Rademacher $\Phi$-type level witness, in [`rademacher_phi_level_witness_mod_oneTwenty_eq_sixtyOne`](thm.html#rademacher_phi_level_witness_mod_oneTwenty_eq_sixtyOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_dedekindSum_of_mul_modEq_one.lean

import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.Data.Int.ModEq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem dedekindSum_of_mul_modEq_one (h h' k : ℕ) (hinv : Nat.ModEq k (h * h') 1) : dedekindSum h' k = dedekindSum h k := by sorry
