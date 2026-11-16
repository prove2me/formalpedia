-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_Supplement_thresholds_below_edge
-- name    : ZigZagStrong.ZigZag.Supplement.thresholds_below_edge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:16:35.638075+00:00
-- url     : https://prove2.me/theorems/a8fb39e7-578d-4d78-a967-653c288f6479
-- title:
--   Corollary 4.5 — every threshold below $\rho_\delta$ is exceeded by order $n$ eigenvalues
-- statement:
--   Under the standing assumptions of §4 with limiting law $D$, let $W_n$ be the normalized adjacency of the configuration multigraph $G_n$. For every fixed $t<\rho_\delta=2\sqrt{\delta-1}/\delta$ there is a constant $c_t>0$ such that, with probability tending to one, at least $c_tn$ eigenvalues of $W_n$ are larger than $t$:
--   $$P\big(\#\{i:\omega_i(W_n)>t\}\ge c_t\,n\big)\xrightarrow[n\to\infty]{}1,$$
--   and in particular
--   $$P\big(\omega_2(W_n)\le t\big)\xrightarrow[n\to\infty]{}0.$$
--   The constant $c_t$ depends only on $D$ and $t$.
--
--   Together with Theorem 4.1 of [CM26], this is what makes the average-degree bound atypical in Theorem 1.4.
--
--   Differences from the source:
--   - generalization: for the fixed sequence of degree sequences, there is c_t > 0 → one c_t > 0, depending on D and t only, serving every sequence of degree sequences satisfying the standing assumptions with limit D; reason: the proof gives c_t = a/(2M) with a = ∫ f dν_D and M = ‖f‖_∞ for a test function f chosen from D and t; the statement for one fixed sequence is a specialization
--   - encoding: at least c_t n eigenvalues of W_n are larger than t → c_t · n ≤ #{eigenvalues ω > t}, counted with multiplicity; reason: same event
--   - encoding: the standing assumptions of §4 (positive degrees, even total degree, uniform bound Δ, empirical degree distribution converging in distribution to D, δ ≥ 2 throughout) → the Prop-structure DegreeRegime deg D, with convergence in distribution written as pointwise convergence of the empirical degree frequencies to D(k); reason: for laws on the nonnegative integers convergence in distribution is equivalent to pointwise convergence of the probability mass functions; each field is one assumption of pp. 15–16
--   - encoding: a uniformly random perfect matching of the N labelled half-edges; loops and multiple edges retained → the uniform law on fixed-point-free involutions of the half-edge type Σ i, Fin (d_i); adjacency A(i,j) counts half-edges of i paired into j, so a loop adds 2 to the diagonal; reason: a perfect matching of a finite set is the same thing as a fixed-point-free involution; the count gives exactly the source adjacency with row sums d_i
--   - encoding: the eigenvalues ω_1 ≥ … ≥ ω_n of W_n and its empirical spectral measure → the multiset of roots of the characteristic polynomial of W_n (n roots since W_n is real symmetric), sorted for ω_2; integrals against the empirical measure written as (1/n) Σ_i f(ω_i); reason: same eigenvalues with multiplicity; the integral of f against (1/n)Σ δ_{ω_i} is that average
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Corollary 4.5, p. 19.

import Definitions.Def_ZigZagStrong_ZigZag_Models
import Definitions.Def_ZigZagStrong_ZigZag_Supplement_GaltonWatson

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag.Supplement
open Filter MeasureTheory
open scoped BigOperators Topology

theorem thresholds_below_edge (D : PMF ℕ) (t : ℝ) (ht : t < edgeValue (minDegree D)) :
    ∃ c_t : ℝ, 0 < c_t ∧ ∀ deg : ∀ n : ℕ, Fin n → ℕ, DegreeRegime deg D →
      Tendsto (fun n => finiteLaw (Ω := Pairing (HalfEdge (deg n)))
        {τ | c_t * (n : ℝ) ≤ (eigCountAbove τ t : ℝ)}) atTop (𝓝 1) ∧
      Tendsto (fun n => finiteLaw (Ω := Pairing (HalfEdge (deg n)))
        {τ | secondEig τ ≤ t}) atTop (𝓝 0) := by sorry

end ZigZagStrong.ZigZag.Supplement
