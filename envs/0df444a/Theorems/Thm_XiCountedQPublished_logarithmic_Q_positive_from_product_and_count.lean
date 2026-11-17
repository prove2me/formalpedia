-- Prove2me | Theorems.Thm_XiCountedQPublished_logarithmic_Q_positive_from_product_and_count
-- name    : XiCountedQPublished.logarithmic_Q_positive_from_product_and_count
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:32:00.48125+00:00
-- url     : https://prove2.me/theorems/812caddf-ece1-4845-b793-557a685667e6
-- title:
--   Positivity of logarithmic Q from a canonical product, counting, and finite spectral verification
-- statement:
--   Let \(\gamma_j\ge2\) and \(|\epsilon_j|\le1/2\), and put \(B_j=\gamma_j^2-\epsilon_j^2-2i\epsilon_j\gamma_j\). Assume \(\epsilon_j=0\) whenever \(\gamma_j\le1000\), and assume an index \(j_0\) satisfies \(\gamma_{j_0}\le100\). Suppose every finite set of indices with \(\gamma_j^2\le y\) has cardinality at most \(y^{3/4}\) for every \(y\ge1\). Let \(c>0\) and \(g(x)>0\) for \(x>0\), with the normalized product identity
--   \[\frac{g(x)}{c}=\prod_j\left(1+\frac{x}{B_j}\right)\quad(x>0).\]
--   Set \(J(x)=\log g(x)-\log c\). Then, for every integer \(n\ge1\) and \(u>0\),
--   \[Q_n(u):=2^n u^{2n-1}(-1)^{n-1}J^{(n)}(u^2)>0.\]
--   The formal index is \(n=r+1\). Gaussian summability, the Gaussian tail bound, reciprocal summability, integrability, and the integral representation of \(Q_n\) are conclusions of the auxiliary results, not independent premises here. The normalized product, counting bound, and finite spectral verification remain explicit hypotheses. No claim is made that those hypotheses have been instantiated in Lean for the complete Riemann-zeta zero multiset, and this theorem does not prove RH.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. PF28 and corrected Branches 2/3. Formalization of classical analytic tools and conditional logarithmic-Q positivity, 2026-11-16. No novelty or RH proof claimed. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem XiCountedQPublished.logarithmic_Q_positive_from_product_and_count (gamma eps : ℕ → ℝ) (hg : ∀ j, 2 ≤ gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ℕ) (anchor_low : gamma anchor ≤ 100)
    (count : ∀ y ≥ (1 : ℝ), ∀ F : Finset ℕ,
      (∀ j ∈ F, (gamma j)^2 ≤ y) → (F.card : ℝ) ≤ y^((3 : ℝ)/4))
    (g : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (gpos : ∀ x > 0, 0 < g x)
    (product_identity : ∀ x > 0, (((g x/c : ℝ) : ℂ)) =
      ∏' j, (1+(x : ℂ)/(((gamma j^2-eps j^2 : ℝ) : ℂ) - ((2*eps j*gamma j : ℝ) : ℂ)*Complex.I)))
    (r : ℕ) (u : ℝ) (hu : 0 < u) :
    0 < (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*(-1 : ℝ)^r *
      iteratedDeriv (r+1) (fun x => Real.log (g x) - Real.log c) (u^2) := by sorry
