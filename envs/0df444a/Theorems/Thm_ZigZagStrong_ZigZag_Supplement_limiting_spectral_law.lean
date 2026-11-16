-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_Supplement_limiting_spectral_law
-- name    : ZigZagStrong.ZigZag.Supplement.limiting_spectral_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:15:28.480678+00:00
-- url     : https://prove2.me/theorems/dd347d7c-75ad-4552-8c94-806cfd2e1f1b
-- title:
--   Proposition 4.3 — existence, uniqueness and weak convergence to $\nu_D$
-- statement:
--   Under the standing assumptions of §4, let $W_n$ be the normalized adjacency of the configuration multigraph $G_n$. There is a unique probability measure $\nu_D$ on $[-1,1]$ whose moments are
--   $$m_k(\nu_D)=\int x^k\,d\nu_D(x)=\mathbb E\,[p_k(T_D,r)]\qquad(k\ge0),$$
--   and the empirical spectral measure $\frac1n\sum_{i=1}^n\delta_{\omega_i(W_n)}$ converges weakly in probability to $\nu_D$: for every bounded continuous $f:\mathbb R\to\mathbb R$,
--   $$\frac1n\sum_{i=1}^n f(\omega_i(W_n))\ \xrightarrow{\ P\ }\ \int f\,d\nu_D.$$
--
--   This is the first clause of Theorem 1.4.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §4 (positive degrees, even total degree, uniform bound Δ, empirical degree distribution converging in distribution to D, δ ≥ 2 throughout) → the Prop-structure DegreeRegime deg D, with convergence in distribution written as pointwise convergence of the empirical degree frequencies to D(k); reason: for laws on the nonnegative integers convergence in distribution is equivalent to pointwise convergence of the probability mass functions; each field is one assumption of pp. 15–16
--   - encoding: a uniformly random perfect matching of the N labelled half-edges; loops and multiple edges retained → the uniform law on fixed-point-free involutions of the half-edge type Σ i, Fin (d_i); adjacency A(i,j) counts half-edges of i paired into j, so a loop adds 2 to the diagonal; reason: a perfect matching of a finite set is the same thing as a fixed-point-free involution; the count gives exactly the source adjacency with row sums d_i
--   - encoding: the unimodular Galton–Watson tree T_D (root with D children, every other vertex D* − 1 children, independently) → Ulam–Harris coding: an independent product law (Measure.infinitePi) on child counts c : List ℕ → ℕ, D at the root address [] and D* − 1 at every other address; vertices are the addresses whose indices are below the parent counts; reason: the standard construction of a Galton–Watson tree; the law of the tree and of every finite neighbourhood is the source one
--   - encoding: the eigenvalues ω_1 ≥ … ≥ ω_n of W_n and its empirical spectral measure → the multiset of roots of the characteristic polynomial of W_n (n roots since W_n is real symmetric), sorted for ω_2; integrals against the empirical measure written as (1/n) Σ_i f(ω_i); reason: same eigenvalues with multiplicity; the integral of f against (1/n)Σ δ_{ω_i} is that average
--   - encoding: a probability measure on [−1, 1] with moments E[p_k(T_D, r)] → IsLimitLaw D ν: a probability measure on ℝ with ν([−1,1]ᶜ) = 0 and ∫ x^k dν = ∫ p_k dT_D for all k ≥ 0; reason: a probability measure on [−1,1] is the same as one on ℝ concentrated there; p_k ∈ [0,1] is a measurable function of finitely many generations, so the integral is the expectation
--   - encoding: the empirical spectral measure converges weakly in probability to ν_D → for every bounded continuous f : ℝ → ℝ, (1/n) Σ_i f(ω_i) converges in probability to ∫ f dν (base ProbConverges under the configuration law); reason: the standard definition of weak convergence in probability of random probability measures
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Proposition 4.3, Eq. (13), p. 18.

import Definitions.Def_ZigZagStrong_ZigZag_Models
import Definitions.Def_ZigZagStrong_ZigZag_Supplement_GaltonWatson

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag.Supplement
open Filter MeasureTheory
open scoped BigOperators Topology BoundedContinuousFunction

theorem limiting_spectral_law (deg : ∀ n : ℕ, Fin n → ℕ) (D : PMF ℕ)
    (hreg : DegreeRegime deg D) :
    ∃ ν : Measure ℝ, IsLimitLaw D ν ∧ (∀ ν' : Measure ℝ, IsLimitLaw D ν' → ν' = ν) ∧
      ∀ f : ℝ →ᵇ ℝ,
        ProbConverges (fun n => finiteLaw (Ω := Pairing (HalfEdge (deg n))))
          (fun _ τ => spectralAverage τ f) (∫ x, f x ∂ν) := by sorry

end ZigZagStrong.ZigZag.Supplement
