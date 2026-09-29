-- Prove2me | Theorems.Thm_syracuse_offset_law_approximation
-- name    : syracuse_offset_law_approximation
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-09T08:16:00.781779+00:00
-- url     : https://prove2.me/theorems/f1f56d52-f3cc-42b5-bb17-9cb042ad802d
-- title:
--   Exponential approximation of the Syracuse offset law
-- statement:
--   Fix c>0 and K≥0. There exist A,d>0, depending only on c,K, with the following property. Let N be a measurable, almost surely positive odd random integer on any probability space. For natural q,t,k, assume (2+c)t≤q and k≤t. Put u_q(r)=2/2^q for odd representatives 0≤r<2^q and zero for even representatives, and assume
--
--   $$\sum_{0\le r<2^q}\left|\Pr(N\equiv r\pmod{2^q})-u_q(r)\right|\le K2^{-q}.$$
--
--   Let G_t have independent positive geometric coordinates with probability 2^{-j} at each integer j≥1, and let F_{t,k} be the Syracuse affine offset in the residue ring modulo 3^k. Then
--
--   $$\sum_{b\in\mathbb{Z}/3^k\mathbb{Z}}\left|\Pr(S^t(N)\equiv b\pmod{3^k})-\Pr(F_{t,k}(G_t)=b)\right|\le A e^{-dt}.$$
--
--   Here S is the Syracuse map. For q>0 the weights u_q form the uniform law on odd residues; for q=0 their sole value is zero, and the gap condition forces t=k=0. All size parameters and probability spaces are quantified after A,d. The comparison is to the geometric-offset law, not to a globally uniform residue law. This conditional estimate transfers the joint valuation approximation to actual modular iterates; it does not assert Collatz convergence or fine-scale mixing.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, Proposition 1.9 and introduction equations (1.21)–(1.22), https://arxiv.org/html/1909.03562v7. The theorem is the finite ZMod(3^k) pushforward of the joint valuation-law estimate through the deterministic Syracuse offset identity.

import Mathlib
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators
open Classical

theorem syracuse_offset_law_approximation (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) : ∃ A d : ℝ, 0 < A ∧ 0 < d ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (N : Ω → ℕ), Measurable N → (∀ᵐ ω ∂μ, 0 < N ω ∧ Odd (N ω)) → ∀ q t k : ℕ, (2 + c) * (t : ℝ) ≤ (q : ℝ) → (∑ r : Fin (2 ^ q), |(μ {ω : Ω | N ω % 2 ^ q = r.val}).toReal - (if Odd r.val then 2 / (2 : ℝ) ^ q else 0)| ≤ K / (2 : ℝ) ^ q) → k ≤ t → (∑ b : ZMod (3 ^ k), |(μ {ω : Ω | ((syracuseStep^[t]) (N ω) : ZMod (3 ^ k)) = b}).toReal - (positiveGeomTwoVector t).real {a | syracuseOffsetMod t k a = b}|) ≤ A * Real.exp (-d * (t : ℝ)) := by sorry
