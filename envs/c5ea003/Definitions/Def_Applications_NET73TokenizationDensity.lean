-- Prove2me | Definitions.Def_Applications_NET73TokenizationDensity
-- name    : Applications_NET73TokenizationDensity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:41.250698+00:00
-- url     : https://prove2.me/theorems/5a797d7f-977e-45ea-88d0-8a5c6b983dcf
-- title:
--   Aether Catalog definitions — Applications_NET73TokenizationDensity
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.NET73TokenizationDensity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/NET73TokenizationDensity.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.NET73

open Finset

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.tail_cons

/-! ## 1. The measured data (four uncensored domains) -/

/-- Domain index: `0 = code`, `1 = prose-de`, `2 = math`, `3 = prose-en`. -/
abbrev Dom := Fin 4

/-- Tokens per word of the fixed BPE tokenizer, per domain. -/
def tpw : Dom → ℚ := ![1950/1000, 1885/1000, 1214/1000, 1173/1000]

/-- Measured knee `k*` at context length 512, per domain. -/
def kneeN : Dom → ℕ := ![12, 20, 16, 16]

/-- The knee as a rational observable (for the regression statistics). -/
def knee : Dom → ℚ := fun i => (kneeN i : ℚ)




/-! ## 2. A general order-theoretic obstruction

If two observables `x` and `y` admit *one* discordant pair, then no strictly
monotone function can carry `x` to `y`.  This is the abstract form of the
NET-73 refutation, and it needs no numerics at all. -/







/-! ## 3. Rank level: competition ranks are monotone invariants -/

/-- Competition rank: `1 +` the number of strictly smaller entries. -/
def crank {n : ℕ} (x : Fin n → ℚ) (i : Fin n) : ℕ :=
  ({j | x j < x i} : Finset (Fin n)).card + 1






/-! ## 4. Spearman rank correlation -/

/-- Spearman's ρ from the sum of squared rank differences (`n` data points). -/
def spearman {n : ℕ} (r s : Fin n → ℚ) : ℚ :=
  1 - 6 * (∑ i, (r i - s i) ^ 2) / ((n : ℚ) * ((n : ℚ) ^ 2 - 1))



/-- Ascending ranks of tokens-per-word: `en < math < de < code`. -/
def rankTpw : Dom → ℚ := ![4, 3, 2, 1]

/-- Ascending ranks of the knee under the experiment's tie-breaking
(`math` before `prose-en` among the two 16's). -/
def rankKnee : Dom → ℚ := ![1, 4, 2, 3]

/-- The opposite tie-breaking (`prose-en` before `math`). -/
def rankKneeAlt : Dom → ℚ := ![1, 4, 3, 2]

/-- Competition ranks (both 16's get rank 2), as produced by `crank`. -/
def rankKneeComp : Dom → ℚ := ![1, 4, 2, 2]

/-- Midrank (tie-averaged) convention. -/
def rankKneeMid : Dom → ℚ := ![1, 4, 5/2, 5/2]




/-! ## 5. Linear regression: the coefficient of determination -/

/-- Sample mean. -/
def mean {n : ℕ} (x : Fin n → ℚ) : ℚ := (∑ i, x i) / (n : ℚ)

/-- (Unnormalised) covariance of two samples. -/
def cov {n : ℕ} (x y : Fin n → ℚ) : ℚ := ∑ i, (x i - mean x) * (y i - mean y)

/-- Coefficient of determination of the least-squares line of `y` on `x`. -/
def rsq {n : ℕ} (x y : Fin n → ℚ) : ℚ := (cov x y) ^ 2 / (cov x x * cov y y)











end Catalog.NET73


