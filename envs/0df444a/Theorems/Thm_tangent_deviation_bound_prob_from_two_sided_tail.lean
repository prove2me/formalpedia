-- Prove2me | Theorems.Thm_tangent_deviation_bound_prob_from_two_sided_tail
-- name    : tangent_deviation_bound_prob_from_two_sided_tail
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-22T06:35:45.472908+00:00
-- url     : https://prove2.me/theorems/b046291e-c464-4014-9773-c3cc17c496c1
-- title:
--   From a two-sided tail to a deviation bound within a budget
-- statement:
--   Deviation-from-tail bridge for the tangent sampling deviation. If the two-sided deviation tail P(|Z - EZ| > t) <= q holds for Z = tangentSamplingDeviation about its Bernoulli mean EZ, and the deterministic budget EZ + t <= bound holds, then the one-sided deviation-bound event P(Z <= bound) has probability at least 1 - q. This is the elementary event-probability step converting a Talagrand/Bennett concentration tail into the TangentSamplingDeviationBound form.
-- source:
--   Candes & Recht, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471, Section 9.1 / proof of Theorem 4.2 (eq. (9.2) tail read off as a deviation bound via the complement of the tail event plus EZ + t <= scale).

import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem tangent_deviation_bound_prob_from_two_sided_tail
    {n1 n2 r : ℕ} {M : RealMatrix n1 n2} (S : SVD M r)
    (p t q bound : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let EZ := bernoulliExpectation p (fun Ω => tangentSamplingDeviation Ω S p)
    bernoulliEventProb p
        (fun Ω => |tangentSamplingDeviation Ω S p - EZ| > t) ≤ q →
    EZ + t ≤ bound →
    bernoulliEventProb p
        (fun Ω => TangentSamplingDeviationBound Ω S p bound) ≥ 1 - q := by sorry
