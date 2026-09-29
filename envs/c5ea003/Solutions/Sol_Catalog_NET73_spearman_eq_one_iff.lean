-- Prove2me | solution 1 for Catalog.NET73.spearman_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:07:47.520876+00:00
-- url     : https://prove2.me/submissions/79de99fc-8409-4265-acfb-3d39dc2ca94d

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















open Catalog.NET73 in
theorem solution{n : ℕ} (hn : 2 ≤ n) (r s : Fin n → ℚ) :
    spearman r s = 1 ↔ r = s := by
  have hn1 : (1 : ℚ) < (n : ℚ) := by
    have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    linarith
  have hpos : 0 < (n : ℚ) * ((n : ℚ) ^ 2 - 1) := by nlinarith
  constructor
  · intro h
    have h0 : 6 * (∑ i, (r i - s i) ^ 2) / ((n : ℚ) * ((n : ℚ) ^ 2 - 1)) = 0 := by
      unfold spearman at h; linarith
    have h1 : 6 * (∑ i, (r i - s i) ^ 2) = 0 :=
      (div_eq_zero_iff.mp h0).resolve_right (ne_of_gt hpos)
    have hsum : (∑ i, (r i - s i) ^ 2) = 0 := by linarith
    funext i
    have hnn : ∀ j ∈ (univ : Finset (Fin n)), 0 ≤ (r j - s j) ^ 2 := fun j _ => sq_nonneg _
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (mem_univ i)
    have hzz : r i - s i = 0 := sq_eq_zero_iff.mp hz
    linarith
  · rintro rfl
    simp [spearman]
