-- Prove2me | solution 1 for Catalog.NET73.rsq_eq_one_of_affine
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:07:46.958785+00:00
-- url     : https://prove2.me/submissions/c80d80b6-aa88-4bec-be7c-8d8060077746

-- Sol generated from Applications/NET73TokenizationDensity.lean
import Mathlib
import Definitions.Def_Applications_NET73TokenizationDensity
/-
# NET-73: Tokenization density does not explain the domain shift

This file formalises the statistical content of the NET-73 experiment
("TOKENIZATION-DENSITY-DOES-NOT-EXPLAIN-THE-DOMAIN-SHIFT").

The experiment measured, for five text domains, the tokens-per-word ratio `TPW`
of one fixed BPE tokenizer on a 5000-word sample, and the *knee* `k*` — the
smallest number of retained attention keys at which model quality saturates at
context length 512.

| domain    | TPW   | k*@512 |
|-----------|-------|--------|
| code      | 1.950 | 12     |
| prose-de  | 1.885 | 20     |
| prose-fr  | 1.246 | > 32   |
| math      | 1.214 | 16     |
| prose-en  | 1.173 | 16     |

`prose-fr` is *censored* (its knee only exceeds the measured grid), so all
numeric statistics below are computed on the four uncensored domains, in the
order `code, prose-de, math, prose-en`; this is exactly the population for which
the experiment reports Spearman ρ = −0.40 and R² = 0.004.  The censored French
point is used separately, as a hypothesis-parameterised strengthening.

What is proved here:

* `Catalog.NET73.no_strictMono_explanation` / `no_strictAnti_explanation` —
  a general order-theoretic obstruction: a single discordant pair forbids *any*
  monotone functional explanation of one observable by another.
* `Catalog.NET73.tokenization_density_no_monotone_law` — the two horns are both
  realised by the data, so no monotone `f` satisfies `k* = f (TPW)`.
* `Catalog.NET73.crank_comp_strictMono` — competition ranks are invariant under
  a strictly monotone reparameterisation, and `crank_knee_ne_crank_tpw` shows
  the observed ranks differ; a rank-level version of the same obstruction.
* `Catalog.NET73.spearman_eq_one_iff` — Spearman ρ = 1 exactly for identical
  rank vectors, together with the three tie-breaking conventions for the data,
  all of which give a *negative* ρ (the reported convention gives exactly
  `-2/5 = -0.40`).
* `Catalog.NET73.rsq_le_one`, `rsq_eq_one_of_affine` (a Cauchy–Schwarz
  argument), the exact value `rsq tpw knee = 4225/1054258 ≈ 0.004008`, and the
  resulting refutation of any affine law `k* = a·TPW + b`.

The companion file `Applications/NET73KneeDecoupling.lean` supplies the
structural side: the knee is governed by attention *concentration*, a relational
quantity that is provably decoupled from tokens-per-word.
-/

open Catalog.NET73

open Finset

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.tail_cons

/-! ## 1. The measured data (four uncensored domains) -/








/-! ## 2. A general order-theoretic obstruction

If two observables `x` and `y` admit *one* discordant pair, then no strictly
monotone function can carry `x` to `y`.  This is the abstract form of the
NET-73 refutation, and it needs no numerics at all. -/







/-! ## 3. Rank level: competition ranks are monotone invariants -/







/-! ## 4. Spearman rank correlation -/












/-! ## 5. Linear regression: the coefficient of determination -/







lemma mean_affine {n : ℕ} (hn : 0 < n) (x : Fin n → ℚ) (a b : ℚ) :
    mean (fun i => a * x i + b) = a * mean x + b := by
  have hn' : ((n : ℚ)) ≠ 0 := by positivity
  unfold mean
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp








open Catalog.NET73 in
theorem solution{n : ℕ} (hn : 0 < n) (x y : Fin n → ℚ) (a b : ℚ)
    (ha : a ≠ 0) (hx : 0 < cov x x) (h : ∀ i, y i = a * x i + b) :
    rsq x y = 1 := by
  have hy : y = fun i => a * x i + b := funext h
  have hmean : mean y = a * mean x + b := by rw [hy]; exact mean_affine hn x a b
  have hcen : ∀ i, y i - mean y = a * (x i - mean x) := by
    intro i; rw [h i, hmean]; ring
  have h1 : cov x y = a * cov x x := by
    unfold cov
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hcen i]; ring
  have h2 : cov y y = a ^ 2 * cov x x := by
    unfold cov
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hcen i]; ring
  unfold rsq
  rw [h1, h2]
  field_simp
