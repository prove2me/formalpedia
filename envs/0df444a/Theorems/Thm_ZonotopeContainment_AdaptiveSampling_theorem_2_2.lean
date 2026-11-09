-- Prove2me | Theorems.Thm_ZonotopeContainment_AdaptiveSampling_theorem_2_2
-- name    : ZonotopeContainment.AdaptiveSampling.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:21:23.12812+00:00
-- url     : https://prove2.me/theorems/04c5457e-fd74-428f-916d-38c724b48f51
-- title:
--   Theorem 2.2 — approximate zonotope containment
-- statement:
--   For every fixed $C\ge64$ there are absolute constants $\eta>0$ and $K>0$ with the following property. Let $d\ge3$, let $w_1,\ldots,w_n\in\mathbb R^d$, and let $T$ be any invertible map satisfying $\tfrac14I\preceq L(Tw)\preceq I$. Let $Q\subseteq\mathbb R^d$ be closed and convex with $0\in\operatorname{int}Q$. For $0<\delta<1$ and every integer
--   $$N\ge Kd(\log d)^4\log(1/\delta),$$
--   test all outputs of $N$ independent runs of Algorithm 1, reusing $T$, by exact membership in $Q$.
--
--   Every recorded point belongs to $Z(w)$ for every realization. Consequently a rejected query exhibits a point of $Z(w)\setminus Q$. If
--   $$Z(w)\not\subseteq\frac2\eta\sqrt{\frac d{\log d}}\,Q,$$
--   then the probability that every query is accepted, and hence that the test incorrectly reports the displayed inclusion, is at most $\delta$.
--
--   No boundedness, polyhedrality or symmetry is imposed on $Q$. The two conclusions establish both soundness of an exhibited witness and the probability bound for a false inclusion report.
--
--   Differences from the source:
--   - encoding: Euclidean vectors, finite generator lists and matrix formulas → EuclideanSpace ℝ (Fin d), Fin n generator families and real matrices acting by toEuclideanLin; reason: these preserve the Euclidean inner product, the ℓ₂ norm and all finite sums
--   - encoding: generator terms divided by their Euclidean norm → zero generators have zero projection and matrix contribution, weight one, and stay zero; reason: deleting or adding zero generators changes neither the zonotope nor any nonzero-generator update
--   - generalization: a fixed absolute algorithm constant C ≥ 64 → every C ≥ 64, with existential constants chosen after C where needed; reason: the analysis fixes C first and chooses the remaining constants afterwards, uniformly in all other data
--   - generalization: rational input matrices and rational-query computational oracle model in §1.1 → arbitrary real generator families and exact membership of the real recorded points; reason: this is the geometric and probabilistic guarantee of the exact Gaussian algorithm; it specializes to rational input without asserting a bit-complexity result
--   - generalization: O(d log⁴d log(1/δ)) independent runs → an absolute K > 0 and every natural N ≥ K d(log d)⁴log(1/δ); reason: it specializes to N = ⌈K d(log d)⁴log(1/δ)⌉; increasing the independent run count can only reduce the probability that all queries are accepted
--   - generalization: T is computed once in a preprocessing step, by approximating Lewis weights (p. 5) → any invertible matrix T with ¼I ⪯ L(Tw) ⪯ I, taken as an input (ApproxLewis w T); its computation is not formalized; reason: Algorithm 1 uses T only through these properties, so the statement covers every map the preprocessing can return
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), Theorem 2.2, p. 6; §1.1, p. 2; Algorithm 1, p. 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm

open MeasureTheory
open scoped Pointwise
open scoped MatrixOrder

namespace ZonotopeContainment.AdaptiveSampling

/-- Theorem 2.2, p. 6: deterministic witnesses and the full failure-probability bound. -/
theorem theorem_2_2 (C : ℝ) (hC : 64 ≤ C) :
    ∃ η : ℝ, 0 < η ∧ ∃ K : ℝ, 0 < K ∧
    ∀ (d n : ℕ), 3 ≤ d → ∀ (w : Fin n → E d) (T : Mat d), ApproxLewis w T →
    ∀ Q : Set (E d), IsClosed Q → Convex ℝ Q → (0 : E d) ∈ interior Q →
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ N : ℕ,
    K * d * (Real.log d) ^ 4 * Real.log (1 / δ) ≤ N →
    (∀ (z : Tapes d N) (k : Fin N) (j : Fin (rounds d)),
      recorded C w T (z k) j ∈ zonotope w) ∧
    (¬ zonotope w ⊆ ((2 / η) * Real.sqrt (d / Real.log d)) • Q →
      runsLaw d N {z | reportsInclusion C w T Q z} ≤ ENNReal.ofReal δ) := by sorry

end ZonotopeContainment.AdaptiveSampling
