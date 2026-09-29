-- Prove2me | Definitions.Def_mme_modern_entropy_data
-- name    : mme_modern_entropy_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T08:33:43.566881+00:00
-- url     : https://prove2.me/theorems/017a2d4f-f0d9-4cf1-9e14-896e9ae35537
-- title:
--   Finite entropy and coordinate marginals for modern laser certificates
-- statement:
--   Let $D$ be a finite set and let $p:D\to\mathbb R$ be a finite real-valued distribution. Its Shannon entropy in bits is defined by
--
--   $$
--   H_2(p)=\frac{-\sum_{a\in D}p(a)\log p(a)}{\log 2},
--   $$
--
--   using the continuous convention $-0\log 0=0$. If $c:D\to I$ is a coordinate map into a finite set $I$, its marginal mass at $i\in I$ is
--
--   $$
--   p_c(i)=\sum_{a\in D:\,c(a)=i}p(a).
--   $$
--
--   These two definitions form the finite data interface used by additive-potential maximum-entropy certificates in modern combination-loss analyses of matrix multiplication.
--
--   **Formalization Note** The entropy definition is meaningful for every real-valued function; subsequent theorem hypotheses impose nonnegativity and total mass one when probability-distribution properties are required.
-- source:
--   E. Dupont et al., Improving the matrix multiplication exponent with modern optimization and AlphaEvolve, arXiv:2608.16884, Section 2.5, Equation (12) and Lemma 1, printed pp. 8–9; https://arxiv.org/abs/2608.16884

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.BigOperators

open BigOperators

universe u v

noncomputable def mme_modern_entropyBits
    {D : Type u} [Fintype D] (p : D → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (p a)) / Real.log 2

noncomputable def mme_modern_marginal
    {D : Type u} {I : Type v} [Fintype D] [DecidableEq I]
    (coord : D → I) (p : D → ℝ) (i : I) : ℝ :=
  ∑ a : {a // coord a = i}, p a


