-- Prove2me | Theorems.Thm_ZonotopeContainment_AdaptiveSampling_proposition_2_1
-- name    : ZonotopeContainment.AdaptiveSampling.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:18:29.022697+00:00
-- url     : https://prove2.me/theorems/0d60743d-da6d-4139-afd5-cb6cc2a6b740
-- title:
--   Proposition 2.1 — single-run guarantee
-- statement:
--   For every fixed $C\ge64$ there is an absolute $c>0$, independent of $d,n,w,T$ and $a$, with the following property. Let $d\ge3$ and let $T$ be an approximate Lewis map for a real generator family $w$. All recorded points of every realization belong to $Z(w)$. For every direction $a\in\mathbb R^d$, one run satisfies
--   $$\mathbb P\left(\exists j<R:\ \langle a,x_{\mathrm{orig},j}\rangle\ge c\sqrt{\frac{\log d}{d}}\,h_{Z(w)}(a)\right)\ge\frac{c}{d(\log d)^4}.$$
--   The number of samples satisfies $R\le1+\log_2\log d$, the explicit form of the source's $O(\log\log d)$. The same $c$ occurs in the height and probability bounds. The zero direction is included. The samples are exactly the $R$ outputs of Algorithm 1.
--
--   Differences from the source:
--   - encoding: Euclidean vectors, finite generator lists and matrix formulas → EuclideanSpace ℝ (Fin d), Fin n generator families and real matrices acting by toEuclideanLin; reason: these preserve the Euclidean inner product, the ℓ₂ norm and all finite sums
--   - encoding: generator terms divided by their Euclidean norm → zero generators have zero projection and matrix contribution, weight one, and stay zero; reason: deleting or adding zero generators changes neither the zonotope nor any nonzero-generator update
--   - generalization: the computational input model uses rational generator matrices → arbitrary real generator families; reason: the geometric and Gaussian statements apply to these families and specialize to rational input
--   - generalization: a fixed absolute algorithm constant C ≥ 64 → every C ≥ 64, with existential constants chosen after C where needed; reason: the analysis fixes C first and chooses the remaining constants afterwards, uniformly in all other data
--   - encoding: a lower bound on the probability of some output meeting the height → an upper bound 1 − c/(d(log d)⁴) (in ℝ≥0∞, truncated at 0) on the probability that every output is strictly below the height; reason: the run law is a probability measure; complementary upper bounds encode the success guarantee without any measurability assumption on the output event
--   - generalization: T is computed once in a preprocessing step, by approximating Lewis weights (p. 5) → any invertible matrix T with ¼I ⪯ L(Tw) ⪯ I, taken as an input (ApproxLewis w T); its computation is not formalized; reason: Algorithm 1 uses T only through these properties, so the statement covers every map the preprocessing can return
--   - encoding: the O(log log d) samples → exactly the R = rounds d recorded points, with the explicit conjunct R ≤ 1 + log₂ log d; reason: R is the exact while-loop count; log₂ log d ≥ log₂ log 3 > 0 for d ≥ 3, so this is the O(log log d) bound with an explicit constant
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), Proposition 2.1, p. 6; proof pp. 8–9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm

open MeasureTheory
open scoped MatrixOrder

namespace ZonotopeContainment.AdaptiveSampling

/-- Proposition 2.1, p. 6: the same c occurs in the height and probability bounds;
the number of samples is the explicit form of O(log log d). -/
theorem proposition_2_1 (C : ℝ) (hC : 64 ≤ C) : ∃ c : ℝ, 0 < c ∧
    ∀ (d n : ℕ), 3 ≤ d → ∀ (w : Fin n → E d) (T : Mat d), ApproxLewis w T →
    (rounds d : ℝ) ≤ 1 + Real.logb 2 (Real.log d) ∧
    (∀ (z : Tape d) (j : Fin (rounds d)), recorded C w T z j ∈ zonotope w) ∧
    ∀ a : E d,
    (runLaw d {z | ∀ j : Fin (rounds d),
      inner ℝ a (recorded C w T z j) < c * Real.sqrt (Real.log d / d) * support w a}) ≤
      1 - ENNReal.ofReal (c / (d * (Real.log d) ^ 4)) := by sorry

end ZonotopeContainment.AdaptiveSampling
