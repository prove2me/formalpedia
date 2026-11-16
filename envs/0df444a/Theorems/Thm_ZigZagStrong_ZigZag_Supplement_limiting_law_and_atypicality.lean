-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_Supplement_limiting_law_and_atypicality
-- name    : ZigZagStrong.ZigZag.Supplement.limiting_law_and_atypicality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:17:14.925075+00:00
-- url     : https://prove2.me/theorems/61cbf29f-2b75-4b2f-8bce-589bcc73f042
-- title:
--   Theorem 1.4 — limiting spectral law $\nu_D$ and atypicality of the average-degree bound
-- statement:
--   Let $d(n)$ be degree sequences satisfying the standing assumptions of §4 (positive, even total degree, uniformly bounded, empirical distribution converging to $D$, $\delta\ge2$), and let $W_n$ be the normalized adjacency of the configuration multigraph $G_n$, with average degree $\bar d=\bar d_n=N_n/n$.
--
--   1. The empirical spectral measure of $W_n$ converges weakly in probability to $\nu_D$, the unique probability measure on $[-1,1]$ whose moments are
--   $$m_k(\nu_D)=\mathbb E\,[p_k(T_D,r)].$$
--   2. $\nu_D$ is symmetric and has support edge
--   $$\rho_\delta:=\frac{2\sqrt{\delta-1}}{\delta},$$
--   that is $\rho(\nu_D)=\rho_\delta$, with $\operatorname{supp}\nu_D\subseteq[-\rho_\delta,\rho_\delta]$ and both endpoints in the support.
--   3. If $D$ is non-constant, there exists $\varepsilon_D>0$ such that
--   $$P\left[\omega_2(W_n)\ge\frac{2\sqrt{\bar d-1}}{\bar d}+\varepsilon_D\right]\xrightarrow[n\to\infty]{}1.$$
--
--   Clause 3 contrasts with the Cohen–Maor existence theorem, which provides for every degree sequence a graph with $\omega_2\le2\sqrt{\bar d-1}/\bar d$: for non-constant limiting degree laws that value is not typical.
--
--   Differences from the source:
--   - generalization: for the fixed sequence of degree sequences, there exists ε_D > 0 → one ε_D > 0, depending on D only, serving every sequence of degree sequences satisfying the standing assumptions with limit D; reason: the subscript D and the proof (p. 20: any t strictly between b(μ) and ρ_δ) make ε_D depend on D alone; the statement for one fixed sequence is a specialization
--   - encoding: D is non-constant → D charges two distinct integers; reason: same condition
--   - encoding: the standing assumptions of §4 (positive degrees, even total degree, uniform bound Δ, empirical degree distribution converging in distribution to D, δ ≥ 2 throughout) → the Prop-structure DegreeRegime deg D, with convergence in distribution written as pointwise convergence of the empirical degree frequencies to D(k); reason: for laws on the nonnegative integers convergence in distribution is equivalent to pointwise convergence of the probability mass functions; each field is one assumption of pp. 15–16
--   - encoding: a uniformly random perfect matching of the N labelled half-edges; loops and multiple edges retained → the uniform law on fixed-point-free involutions of the half-edge type Σ i, Fin (d_i); adjacency A(i,j) counts half-edges of i paired into j, so a loop adds 2 to the diagonal; reason: a perfect matching of a finite set is the same thing as a fixed-point-free involution; the count gives exactly the source adjacency with row sums d_i
--   - encoding: the unimodular Galton–Watson tree T_D (root with D children, every other vertex D* − 1 children, independently) → Ulam–Harris coding: an independent product law (Measure.infinitePi) on child counts c : List ℕ → ℕ, D at the root address [] and D* − 1 at every other address; vertices are the addresses whose indices are below the parent counts; reason: the standard construction of a Galton–Watson tree; the law of the tree and of every finite neighbourhood is the source one
--   - encoding: the eigenvalues ω_1 ≥ … ≥ ω_n of W_n and its empirical spectral measure → the multiset of roots of the characteristic polynomial of W_n (n roots since W_n is real symmetric), sorted for ω_2; integrals against the empirical measure written as (1/n) Σ_i f(ω_i); reason: same eigenvalues with multiplicity; the integral of f against (1/n)Σ δ_{ω_i} is that average
--   - encoding: a probability measure on [−1, 1] with moments E[p_k(T_D, r)] → IsLimitLaw D ν: a probability measure on ℝ with ν([−1,1]ᶜ) = 0 and ∫ x^k dν = ∫ p_k dT_D for all k ≥ 0; reason: a probability measure on [−1,1] is the same as one on ℝ concentrated there; p_k ∈ [0,1] is a measurable function of finitely many generations, so the integral is the expectation
--   - encoding: the empirical spectral measure converges weakly in probability to ν_D → for every bounded continuous f : ℝ → ℝ, (1/n) Σ_i f(ω_i) converges in probability to ∫ f dν (base ProbConverges under the configuration law); reason: the standard definition of weak convergence in probability of random probability measures
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Theorem 1.4, Eqs. (4)–(5), p. 6 (proved in §4, pp. 15–20).

import Definitions.Def_ZigZagStrong_ZigZag_Models
import Definitions.Def_ZigZagStrong_ZigZag_Supplement_GaltonWatson

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag.Supplement
open Filter MeasureTheory
open scoped BigOperators Topology BoundedContinuousFunction

theorem limiting_law_and_atypicality (D : PMF ℕ) :
    (∀ deg : ∀ n : ℕ, Fin n → ℕ, DegreeRegime deg D →
      ∃ ν : Measure ℝ, IsLimitLaw D ν ∧ (∀ ν' : Measure ℝ, IsLimitLaw D ν' → ν' = ν) ∧
        (∀ f : ℝ →ᵇ ℝ,
          ProbConverges (fun n => finiteLaw (Ω := Pairing (HalfEdge (deg n))))
            (fun _ τ => spectralAverage τ f) (∫ x, f x ∂ν)) ∧
        ν.map (fun x => -x) = ν ∧
        supportEdge ν = edgeValue (minDegree D) ∧
        ν.support ⊆ Set.Icc (-edgeValue (minDegree D)) (edgeValue (minDegree D)) ∧
        edgeValue (minDegree D) ∈ ν.support ∧ -edgeValue (minDegree D) ∈ ν.support) ∧
    ((∃ a b : ℕ, a ≠ b ∧ D a ≠ 0 ∧ D b ≠ 0) →
      ∃ ε_D : ℝ, 0 < ε_D ∧ ∀ deg : ∀ n : ℕ, Fin n → ℕ, DegreeRegime deg D →
        Tendsto (fun n => finiteLaw (Ω := Pairing (HalfEdge (deg n)))
          {τ | edgeValue (avgDegree (deg n)) + ε_D ≤ secondEig τ}) atTop (𝓝 1)) := by sorry

end ZigZagStrong.ZigZag.Supplement
