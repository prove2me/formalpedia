-- Prove2me | Theorems.Thm_GammaPositivity_IsGammaPositive_mul
-- name    : GammaPositivity.IsGammaPositive.mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:37:54.864608+00:00
-- url     : https://prove2.me/theorems/02167067-6246-4d74-9911-10b946fb746f
-- title:
--   γ-positivity is multiplicative across orders.
-- statement:
--   **γ-positivity is multiplicative across orders.**
--   If `p` is γ-positive of order `m` and `q` is γ-positive of order `n`, then `p * q`
--   is γ-positive of order `m + n`.
--
--   ```lean
--   theorem GammaPositivity.IsGammaPositive.mul{m n : ℕ} {p q : ℝ[X]}
--       (hp : IsGammaPositive m p) (hq : IsGammaPositive n q) :
--       IsGammaPositive (m + n) (p * q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/GammaPositivityProduct.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/GammaPositivityProduct.lean#L67

-- Thm stub generated from Probability/GammaPositivityProduct.lean
import Mathlib
import Definitions.Def_Probability_GammaPositivity

/-!
# γ-positivity is a graded cone: closure under sum and product

The γ-positive polynomials of a fixed order form a convex cone, and — remarkably —
γ-positivity is *multiplicative* across orders: the product of a γ-positive
polynomial of order `m` and a γ-positive polynomial of order `n` is γ-positive of
order `m + n`.  This is the algebraic backbone behind the fact that γ-positivity of
Ehrhart `h*`-polynomials is preserved under the *free join / product* operations on
symmetric edge polytopes, and it is the tool one uses to lift γ-positivity from small
building blocks to large graphs.

The engine is the identity
`(t^i (1+t)^{m-2i}) · (t^j (1+t)^{n-2j}) = t^{i+j} (1+t)^{(m+n)-2(i+j)}`,
which says the γ-basis is closed under multiplication with additive indices.

Main results:

* `gammaBasis_mul` — the γ-basis multiplies index-additively;
* `IsGammaPositive.add` — closure of order-`n` γ-positive polynomials under addition;
* `IsGammaPositive.mul` — **closure under product across orders** (flagship result).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the γ-basis is a "monomial-like" family closed under
multiplication, so γ-positivity should behave like nonnegativity of coefficients in a
graded polynomial ring — closed under both `+` and `×`.
Experiment (Experimenter): checked `B_m i · B_n j = B_{m+n}(i+j)` symbolically; the
exponent bookkeeping `(m-2i)+(n-2j) = (m+n)-2(i+j)` holds precisely when `2i ≤ m` and
`2j ≤ n`, which is exactly the support constraint of a γ-expansion.
Analysis (Analyst): the product of two γ-expansions is a double sum of basis elements
indexed by `(i,j)`; regrouping by the fibre `i+j = l` (a `sum_fiberwise` argument)
recovers a genuine order-`(m+n)` γ-expansion with coefficients
`γ_l = Σ_{i+j=l} a_i b_j ≥ 0`.
Critique (Critic): the regrouping only closes if the fibre map `(i,j) ↦ i+j` lands in
`range((m+n)/2+1)`; this needs `i ≤ m/2, j ≤ n/2 ⟹ i+j ≤ (m+n)/2`, verified by `omega`.
Synthesis: γ-positive polynomials form a graded (ℕ-indexed) cone under `+` within an
order and `×` across orders — a clean structural strengthening of the palindromicity
results in `GammaPositivity.lean`.
-/

open GammaPositivity

open Polynomial BigOperators

theorem GammaPositivity.IsGammaPositive.mul{m n : ℕ} {p q : ℝ[X]}
    (hp : IsGammaPositive m p) (hq : IsGammaPositive n q) :
    IsGammaPositive (m + n) (p * q) := by sorry
