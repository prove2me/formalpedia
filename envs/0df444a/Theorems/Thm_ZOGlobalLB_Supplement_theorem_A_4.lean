-- Prove2me | Theorems.Thm_ZOGlobalLB_Supplement_theorem_A_4
-- name    : ZOGlobalLB.Supplement.theorem_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:53:02.009989+00:00
-- url     : https://prove2.me/theorems/e0952d74-42b8-486c-ac48-4009f12d3ae2
-- title:
--   Theorem A.4 — adaptive Gaussian likelihood and score chain rule
-- statement:
--   Let $v$ be a smooth parameter and let $(Y_i)_{i\le n}$ be an adaptive transcript. Conditional on the previous responses and $v$, suppose each response is either a parameter-independent point mass or Gaussian with history-measurable variance $s_i^2>0$ and differentiable conditional mean $m_i(v)$. The branch, variance, and deterministic response depend only on the realized history. Assume the total score energy is finite.
--
--   Holding each history fixed when differentiating, the log-likelihood score is
--
--   $$
--   \nabla_v\log p(T_n\mid v)=\sum_{i=1}^n S_i,
--   \qquad
--   S_i=\frac{Y_i-m_i(v)}{s_i^2}\nabla_vm_i(v)
--   $$
--
--   at Gaussian rounds and $S_i=0$ at deterministic rounds. Moreover,
--
--   $$
--   \mathbb E[S_i\mid v,T_{i-1}]=0,
--   \qquad
--   \mathbb E[\|S_i\|^2\mid v,T_{i-1}]=\frac{\|\nabla_vm_i(v)\|^2}{s_i^2},
--   $$
--
--   with zero on deterministic rounds. Scores from distinct rounds are orthogonal in $L^2$, and the squared $L^2$ norm of their sum is the sum of their squared norms. No independence of adaptive query locations or positive uniform lower bound on nonzero variances is assumed.
--
--   Differences from the source:
--   - encoding: a parameter on a smooth manifold → its finite-dimensional Euclidean tangent coordinate chart at the candidate parameter; reason: the theorem is local in $v$ and every displayed gradient and score is exactly its chart-coordinate representative
--   - encoding: a history-conditional Gaussian kernel → $m_i(v,h)+\sqrt{s_i^2(h)}Z_i$ with a standard normal innovation independent of the realized past; reason: every such conditional Gaussian kernel admits this realization on an extension and it changes no transcript law
--   - encoding: conditional expectations → equality against every bounded measurable function of the past; reason: this is the version-independent defining characterization of the same conditional moments
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem A.4, pp.34-35

import Mathlib
import Definitions.Def_ZOGlobalLB_Supplement_adaptiveScore

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

universe u

namespace ZOGlobalLB

namespace Supplement

/-- **Theorem A.4 (Adaptive Gaussian likelihood and score chain rule).** Xia, Yuan,
*On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization*, arXiv:2610.19652,
Theorem A.4, pp.34--35.

For a finite adaptive transcript whose next response, conditional on the past, is either a
parameter-independent point mass or a Gaussian with positive history-dependent variance and a
differentiable conditional mean, the log-likelihood score is the sum of the conditional scores.
The scores have conditional mean zero and the displayed conditional second moment, are pairwise
orthogonal in `L²`, and hence their squared `L²` norms add.

**Formalization Note.** A smooth parameter is expressed in a Euclidean coordinate chart `E p`,
which is the tangent-coordinate reading of the paper's manifold notation. A conditional Gaussian
response is realized as `m_i(v,h) + sqrt(s_i²(h)) Z_i`, where `Z_i` has standard normal law and is
independent of the realized past; every such conditional Gaussian kernel has this realization on
an extension. The branch, variance, and deterministic response are functions only of history.
The conditional-moment conclusions use their defining bounded-test-function identities, avoiding
any version choice for conditional expectation. -/
theorem theorem_A_4 {n p : ℕ} (v : E p) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (branch : (i : Fin n) → (Fin i.val → ℝ) → Bool)
    (variance : (i : Fin n) → (Fin i.val → ℝ) → ℝ)
    (mean : (i : Fin n) → (Fin i.val → ℝ) → E p → ℝ)
    (deterministic : (i : Fin n) → (Fin i.val → ℝ) → ℝ)
    (Y : Ω → Fin n → ℝ) (Z : Fin n → Ω → ℝ)
    (hbranch : ∀ i, Measurable (branch i))
    (hvariance : ∀ i, Measurable (variance i))
    (hdet : ∀ i, Measurable (deterministic i))
    (hYmeas : ∀ i, Measurable fun ω => Y ω i)
    (hmeanMeas : ∀ i w, Measurable fun h => mean i h w)
    (hmean : ∀ i h, DifferentiableAt ℝ (mean i h) v)
    (hpos : ∀ i h, branch i h = true → 0 < variance i h)
    (hY : ∀ ω i, Y ω i =
      if branch i (transcriptPrefix Y i ω) then
        mean i (transcriptPrefix Y i ω) v +
          Real.sqrt (variance i (transcriptPrefix Y i ω)) * Z i ω
      else deterministic i (transcriptPrefix Y i ω))
    (hZmeas : ∀ i, Measurable (Z i))
    (hZlaw : ∀ i, HasLaw (Z i) (gaussianReal 0 1) P)
    (hZpast : ∀ i, IndepFun (Z i) (transcriptPrefix Y i) P)
    (henergy : (∑ i, ∫⁻ ω, ENNReal.ofReal
      (if branch i (transcriptPrefix Y i ω) then
        ‖gradient (mean i (transcriptPrefix Y i ω)) v‖ ^ 2 /
          variance i (transcriptPrefix Y i ω)
       else 0) ∂P) ≠ ⊤) :
    (∀ᵐ ω ∂P,
      gradient (fun w : E p => ∑ i,
        if branch i (transcriptPrefix Y i ω) then
          -(Y ω i - mean i (transcriptPrefix Y i ω) w) ^ 2 /
            (2 * variance i (transcriptPrefix Y i ω))
        else 0) v =
      ∑ i, adaptiveScore v branch variance mean Y i ω) ∧
    (∀ (i : Fin n) (φ : (Fin i.val → ℝ) → ℝ), Measurable φ →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ h, |φ h| ≤ M) →
      Integrable (fun ω => φ (transcriptPrefix Y i ω) •
        adaptiveScore v branch variance mean Y i ω) P ∧
      (∫ ω, φ (transcriptPrefix Y i ω) •
        adaptiveScore v branch variance mean Y i ω ∂P) = 0 ∧
      Integrable (fun ω => φ (transcriptPrefix Y i ω) *
        ‖adaptiveScore v branch variance mean Y i ω‖ ^ 2) P ∧
      (∫ ω, φ (transcriptPrefix Y i ω) *
          ‖adaptiveScore v branch variance mean Y i ω‖ ^ 2 ∂P) =
        ∫ ω, φ (transcriptPrefix Y i ω) *
          (if branch i (transcriptPrefix Y i ω) then
            ‖gradient (mean i (transcriptPrefix Y i ω)) v‖ ^ 2 /
              variance i (transcriptPrefix Y i ω)
           else 0) ∂P) ∧
    (∀ i j : Fin n, i ≠ j →
      Integrable (fun ω =>
        inner ℝ (adaptiveScore v branch variance mean Y i ω)
          (adaptiveScore v branch variance mean Y j ω)) P ∧
      (∫ ω,
        inner ℝ (adaptiveScore v branch variance mean Y i ω)
          (adaptiveScore v branch variance mean Y j ω) ∂P) = 0) ∧
    Integrable (fun ω => ‖∑ i, adaptiveScore v branch variance mean Y i ω‖ ^ 2) P ∧
    (∫ ω, ‖∑ i, adaptiveScore v branch variance mean Y i ω‖ ^ 2 ∂P) =
      ∑ i, ∫ ω, ‖adaptiveScore v branch variance mean Y i ω‖ ^ 2 ∂P := by sorry

end Supplement

end ZOGlobalLB
