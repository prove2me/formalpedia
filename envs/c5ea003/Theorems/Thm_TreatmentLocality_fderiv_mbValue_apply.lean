-- Prove2me | Theorems.Thm_TreatmentLocality_fderiv_mbValue_apply
-- name    : TreatmentLocality.fderiv_mbValue_apply
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T00:36:04.677087+00:00
-- url     : https://prove2.me/theorems/2392313b-9c42-4c36-a64a-7bce8fd2de64
-- title:
--   Gradient of the model-based plug-in estimator
-- statement:
--   **The gradient of the model-based plug-in estimator.** Fix an SST model $M$ with discount factor $\gamma$ and a statistics vector $v$ at which every visit count $N^a_i = \sum_k K^a_{ik}$ is nonzero and the plug-in Bellman system matrix $B = \mathrm{Diag}(N^a) - \gamma K^a$ is invertible. Then the plug-in value function $\hat V^a_s$ is Fréchet differentiable in the statistics, and its derivative in the direction $h = (\mathrm{d}K, \mathrm{d}R)$ is
--   $$\mathrm{d}\hat V^a_s[h] \;=\; \Bigl(B^{-1} w\Bigr)_s, \qquad w_i \;=\; \mathrm{d}R^a_i + \sum_j \mathrm{d}K^a_{ij}\,\bigl(\gamma \hat V^a_j - \hat V^a_i\bigr).$$
--
--   Two features of the formula matter. First, the derivative is again obtained by solving the same linear system, with a modified right-hand side — no separate resolvent appears. Second, the perturbation of the transition counts enters only through the **temporal-difference residual** $\gamma \hat V^a_j - \hat V^a_i$: the Bellman equation $\hat r^a_i + \gamma(\hat P^a \hat V^a)_i = \hat V^a_i$ makes the terms that would otherwise come from renormalising the rows cancel exactly. This is the gradient the delta method requires in order to turn a central limit theorem for the statistics into one for the estimator (arXiv:2407.19618, Lemma EC.5 and Theorems 3-4), and it is the object whose asymptotic covariance is the matrix $\Sigma_{IS}$.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3: Section 2 (V = (I - γP)⁻¹ r), Remark 1 and Proposition 5 (the plug-in estimators P̂, r̂, V̂), Appendix EC.6 eq. (EC.4) (the visit-count weighted system), and Appendix EC.4.3, where the same derivatives ∂Δ/∂P(s,j) = γ(I - γP)⁻¹E_{s,j}V and ∂Δ/∂r are computed for the constrained Cramér-Rao bound of Theorem 5.

import Definitions.Def_TreatmentLocalityPlugIn

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.fderiv_mbValue_apply {S : Type*} [DecidableEq S] [Fintype S]
    (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) (hB : IsUnit (mbSystem M v a)) (s : S) (h : EstInput S) :
    fderiv ℝ (fun u : EstInput S => mbValue M u a s) v h
      = ((mbSystem M v a)⁻¹.mulVec (fun i =>
          (h a).2 i + ∑ j, (h a).1 i j *
            (M.γdisc * mbValue M v a j - mbValue M v a i))) s := by sorry
