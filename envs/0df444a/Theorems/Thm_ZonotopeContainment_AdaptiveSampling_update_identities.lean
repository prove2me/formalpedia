-- Prove2me | Theorems.Thm_ZonotopeContainment_AdaptiveSampling_update_identities
-- name    : ZonotopeContainment.AdaptiveSampling.update_identities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:22:57.595196+00:00
-- url     : https://prove2.me/theorems/37174f44-b88d-4f2f-a11f-43fc6afd329c
-- title:
--   §2.1 (p. 6) — norm and support-loss identities
-- statement:
--   Let $v_1,\ldots,v_n$ span $\mathbb R^d$ and let $0<r_i\le1$. Put $S=\sum_i r_iv_iv_i^\top/\|v_i\|$, $v_i^+=r_iS^{-1/2}v_i$ and $b^+=S^{1/2}b$. For every $b\in\mathbb R^d$,
--   $$\|b^+\|^2=b^\top Sb,\qquad h_{Z(v)}(b)-h_{Z(v^+)}(b^+)=\sum_i(1-r_i)|\langle b,v_i\rangle|.$$
--   These equalities express both quantities appearing in the good-update lemma in terms of a single set of shortening weights.
--
--   Differences from the source:
--   - encoding: Euclidean vectors, finite generator lists and matrix formulas → EuclideanSpace ℝ (Fin d), Fin n generator families and real matrices acting by toEuclideanLin; reason: these preserve the Euclidean inner product, the ℓ₂ norm and all finite sums
--   - encoding: generator terms divided by their Euclidean norm → zero generators contribute zero to S and stay zero, whatever their weight; reason: deleting or adding zero generators changes neither the zonotope nor any nonzero-generator update
--   - generalization: the algorithm weights qᵢ and the functional b = Aᵀa at a current iteration with d ≥ 3 → arbitrary weights 0 < rᵢ ≤ 1, every functional b and spanning real generators in any finite dimension; reason: both identities are algebraic consequences of a positive weighted matrix and specialize to the algorithm weights
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), §2.1, p. 6, display after “Indeed we have that”; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm

open scoped BigOperators
open scoped MatrixOrder

namespace ZonotopeContainment.AdaptiveSampling

/-- §2.1, p. 6: the identities for all positive shortening weights. -/
theorem update_identities (d n : ℕ) (v : Fin n → E d)
    (hv : Submodule.span ℝ (Set.range v) = ⊤) (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i ∧ r i ≤ 1) (b : E d) :
    ‖act (CFC.sqrt (weightedMatrix v r)) b‖ ^ 2 =
      inner ℝ b (act (weightedMatrix v r) b) ∧
    support v b - support (updatedGenerators v r)
      (act (CFC.sqrt (weightedMatrix v r)) b) =
      ∑ i, (1 - r i) * |inner ℝ b (v i)| := by sorry

end ZonotopeContainment.AdaptiveSampling
