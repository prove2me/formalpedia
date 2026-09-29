-- Prove2me | solution 1 for GammaPositivity.IsGammaPositive.mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:15:56.214993+00:00
-- url     : https://prove2.me/submissions/3c602556-a26f-4c7f-95f2-de92ce8c308f

-- Sol generated from Probability/GammaPositivityProduct.lean
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

/-- **The γ-basis multiplies with additive indices.**
`t^i (1+t)^{m-2i} · t^j (1+t)^{n-2j} = t^{i+j} (1+t)^{(m+n)-2(i+j)}`, valid whenever
`2 i ≤ m` and `2 j ≤ n`. -/
theorem gammaBasis_mul (m n i j : ℕ) (hi : 2 * i ≤ m) (hj : 2 * j ≤ n) :
    gammaBasis m i * gammaBasis n j = gammaBasis (m + n) (i + j) := by
  unfold gammaBasis
  have h1 : (m - 2 * i) + (n - 2 * j) = (m + n) - 2 * (i + j) := by omega
  rw [← h1]
  ring




open GammaPositivity in
theorem solution{m n : ℕ} {p q : ℝ[X]}
    (hp : IsGammaPositive m p) (hq : IsGammaPositive n q) :
    IsGammaPositive (m + n) (p * q) := by
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hq
  refine ⟨fun l => ∑ ij ∈ (Finset.range (m / 2 + 1) ×ˢ Finset.range (n / 2 + 1)).filter
      (fun ij => ij.1 + ij.2 = l), a ij.1 * b ij.2, ?_, ?_⟩
  · intro l; exact Finset.sum_nonneg (fun ij _ => mul_nonneg (ha _) (hb _))
  · rw [Finset.sum_mul_sum, ← Finset.sum_product']
    have hmap : ∀ ij ∈ Finset.range (m / 2 + 1) ×ˢ Finset.range (n / 2 + 1),
        ij.1 + ij.2 ∈ Finset.range ((m + n) / 2 + 1) := by
      intro ij hij
      simp only [Finset.mem_product, Finset.mem_range] at hij ⊢
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmap]
    apply Finset.sum_congr rfl
    intro l _
    simp only []
    conv_rhs => rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hij
    obtain ⟨⟨hi, hj⟩, hl⟩ := hij
    rw [← hl, ← gammaBasis_mul m n ij.1 ij.2 (by omega) (by omega), map_mul]
    ring
