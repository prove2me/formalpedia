-- Prove2me | Theorems.Thm_XiCountedQPublished_gaussian_tail_from_count
-- name    : XiCountedQPublished.gaussian_tail_from_count
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:31:40.081213+00:00
-- url     : https://prove2.me/theorems/b4fd272f-592f-4549-9551-8cba3d07ebd1
-- title:
--   Gaussian spectral tail from a quadratic counting bound with a strict cutoff
-- statement:
--   Let \((\gamma_j)_{j\ge0}\) be a nonnegative real sequence. Suppose that for every \(T\ge10\), every finite set of indices whose heights are at most \(T\) has cardinality at most \(T^2\). Then, for every \(t>0\), the Gaussian series is summable, and for every \(L\ge10\),
--   \[\sum_{\gamma_j>L}e^{-t\gamma_j^2}\le (L^2+t^{-1})e^{-tL^2}.\]
--   The cutoff is strict. Repeated heights are counted through their indices, so the statement allows multiplicities. This is a theorem for a general sequence under a counting hypothesis; it does not itself establish that hypothesis for the zeta zeros.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. PF28 and corrected Branches 2/3. Formalization of classical analytic tools and conditional logarithmic-Q positivity, 2026-11-16. No novelty or RH proof claimed. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem XiCountedQPublished.gaussian_tail_from_count (gamma : ℕ → ℝ) (hg : ∀ j, 0 ≤ gamma j)
    (hcount : ∀ T ≥ (10 : ℝ), ∀ F : Finset ℕ,
      (∀ j ∈ F, gamma j ≤ T) → (F.card : ℝ) ≤ T^2) :
    (∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t))) ∧
    (∀ t > 0, ∀ L ≥ (10 : ℝ),
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
        (L^2+t⁻¹)*Real.exp (-L^2*t)) := by sorry
