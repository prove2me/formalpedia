-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_Supplement_support_edge
-- name    : ZigZagStrong.ZigZag.Supplement.support_edge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:15:53.937021+00:00
-- url     : https://prove2.me/theorems/b91b5388-87c3-49a7-89b1-e3199fa4848c
-- title:
--   Lemma 4.4 — symmetry and support edge $\rho_\delta=2\sqrt{\delta-1}/\delta$ of $\nu_D$
-- statement:
--   Let $D$ be a probability law on the positive integers with bounded support and minimum degree $\delta\ge2$, and let $\nu_D$ be its limit law (the probability measure on $[-1,1]$ with moments $\mathbb E[p_k(T_D,r)]$). Then $\nu_D$ is symmetric, $\nu_D(-A)=\nu_D(A)$, and
--   $$\rho(\nu_D)=\rho_\delta:=\frac{2\sqrt{\delta-1}}{\delta};$$
--   equivalently $\operatorname{supp}\nu_D\subseteq[-\rho_\delta,\rho_\delta]$ and both endpoints $\pm\rho_\delta$ belong to the support.
--
--   The paper states this lemma and cites it from Müller and Wiegel [MW20, Lemma 6.5]. It gives the symmetry and support-edge clause of Theorem 1.4.
--
--   Differences from the source:
--   - encoding: the limiting law ν_D of a law D arising under the standing assumptions of §4 → hypotheses on D alone (D(0) = 0, bounded support, δ ≥ 2) and any ν with IsLimitLaw D ν; reason: under the standing assumptions D is exactly such a law, and every such law is the limit of some admissible degree sequences; ν_D is the unique limit law (Proposition 4.3)
--   - encoding: ρ(ν) = max{|x| : x ∈ supp ν} → supportEdge ν = sSup of |x| over the support, stated together with the equivalent form (support inside [−ρ_δ, ρ_δ], both endpoints in it); reason: the support is closed and bounded, so the supremum is the maximum; the endpoint clauses make attainment explicit
--   - encoding: the unimodular Galton–Watson tree T_D (root with D children, every other vertex D* − 1 children, independently) → Ulam–Harris coding: an independent product law (Measure.infinitePi) on child counts c : List ℕ → ℕ, D at the root address [] and D* − 1 at every other address; vertices are the addresses whose indices are below the parent counts; reason: the standard construction of a Galton–Watson tree; the law of the tree and of every finite neighbourhood is the source one
--   - encoding: a probability measure on [−1, 1] with moments E[p_k(T_D, r)] → IsLimitLaw D ν: a probability measure on ℝ with ν([−1,1]ᶜ) = 0 and ∫ x^k dν = ∫ p_k dT_D for all k ≥ 0; reason: a probability measure on [−1,1] is the same as one on ℝ concentrated there; p_k ∈ [0,1] is a measurable function of finitely many generations, so the integral is the expectation
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Lemma 4.4, Eq. (14), p. 19 (citing [MW20, Lemma 6.5]).

import Definitions.Def_ZigZagStrong_ZigZag_Models
import Definitions.Def_ZigZagStrong_ZigZag_Supplement_GaltonWatson

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag.Supplement
open Filter MeasureTheory
open scoped BigOperators Topology

theorem support_edge (D : PMF ℕ) (h0 : D 0 = 0) (hbdd : ∃ Δ : ℕ, ∀ k : ℕ, Δ < k → D k = 0)
    (hδ : 2 ≤ minDegree D) (ν : Measure ℝ) (hν : IsLimitLaw D ν) :
    ν.map (fun x => -x) = ν ∧
      supportEdge ν = edgeValue (minDegree D) ∧
      ν.support ⊆ Set.Icc (-edgeValue (minDegree D)) (edgeValue (minDegree D)) ∧
      edgeValue (minDegree D) ∈ ν.support ∧ -edgeValue (minDegree D) ∈ ν.support := by sorry

end ZigZagStrong.ZigZag.Supplement
