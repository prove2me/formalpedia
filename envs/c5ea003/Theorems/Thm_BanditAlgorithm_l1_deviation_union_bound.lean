-- Prove2me | Theorems.Thm_BanditAlgorithm_l1_deviation_union_bound
-- name    : BanditAlgorithm.l1_deviation_union_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T03:56:23.331798+00:00
-- url     : https://prove2.me/theorems/27f7bd1f-8ce9-48c1-8d4b-4dbde278bde4
-- title:
--   Union bound over events turns a scalar tail into an $\ell_1$ tail
-- statement:
--   Let $\hat p_\omega$ and $p$ be real vectors on a finite set $\iota$ carrying the same total mass for every $\omega$ — in particular two probability vectors. If every event $A \subseteq \iota$ satisfies
--
--   $$\mathbb{P}\Big(\hat p(A) - p(A) \ge \tfrac{\varepsilon}{2}\Big) \le b,$$
--
--   then
--
--   $$\mathbb{P}\big(\|\hat p - p\|_1 \ge \varepsilon\big) \;\le\; 2^{|\iota|}\, b.$$
--
--   This is the reduction that turns the scalar concentration of event probabilities into the $\ell^1$ concentration required by the confidence sets of UCRL2 (Lattimore and Szepesvári, Eq. 38.13 and Lemma 38.8). It carries no probabilistic content of its own: it is the variational identity $\|\hat p - p\|_1 = 2\max_{A}(\hat p(A) - p(A))$ followed by a union bound over the $2^{|\iota|}$ subsets of $\iota$. The factor $2^{S}$ it produces is exactly what appears as the $S$ inside the logarithm of the UCRL2 confidence width $\sqrt{S L_t(s,a)/(1 \vee T_t(s,a))}$.
--
--   The proof: for each $\omega$ with $\|\hat p_\omega - p\|_1 \ge \varepsilon$ the variational identity supplies an event $A$ (namely $\{a : p_a \le \hat p_\omega(a)\}$) with $2(\hat p_\omega(A) - p(A)) = \|\hat p_\omega - p\|_1 \ge \varepsilon$, so the deviation event is contained in the union over $A$ of the scalar deviation events; subadditivity over the finitely many subsets, of which there are $2^{|\iota|}$, finishes the argument.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Exercise 38.21 and Lemma 38.8 (confidence sets of UCRL2, Eq. 38.13); Weissman, Ordentlich, Seroussi, Verdu & Weinberger, Inequalities for the L1 deviation of the empirical distribution, HP Labs Tech. Report HPL-2003-97 (2003).

import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory

theorem BanditAlgorithm.l1_deviation_union_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (phat : Ω → ι → ℝ) (p : ι → ℝ) (ε b : ℝ)
    (hsum : ∀ ω, ∑ a, phat ω a = ∑ a, p a)
    (hbound : ∀ A : Finset ι, μ.real {ω | ε / 2 ≤ ∑ a ∈ A, (phat ω a - p a)} ≤ b) :
    μ.real {ω | ε ≤ ∑ a, |phat ω a - p a|} ≤ 2 ^ Fintype.card ι * b := by
  sorry
