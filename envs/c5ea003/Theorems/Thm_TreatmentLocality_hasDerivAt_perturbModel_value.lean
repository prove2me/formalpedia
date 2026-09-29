-- Prove2me | Theorems.Thm_TreatmentLocality_hasDerivAt_perturbModel_value
-- name    : TreatmentLocality.hasDerivAt_perturbModel_value
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T14:56:46.823441+00:00
-- url     : https://prove2.me/theorems/8a4d1369-f560-42a9-8fc5-008c50f5d87f
-- title:
--   Derivative of a policy value along a model perturbation
-- statement:
--   **The derivative of a policy value along a perturbation of the model.** Let $M$ be an SST model of arXiv:2407.19618 with Gaussian rewards, and move it along a direction $(\alpha,\beta)$ whose transition part is centred: at parameter $t$ the mean reward at $(s,a)$ becomes $m(s,a) + t\,\alpha(s,a)\sigma^2(s,a)$ and the transition row becomes $P(\cdot\mid s,a)(1 + t\,\beta(s,a,\cdot))$. Then the value function of the policy that plays arm $a$ is differentiable at $t = 0$ with
--   $$\frac{\mathrm d}{\mathrm d t}\Big|_{0} V^a_t \;=\; (I - \gamma P^a)^{-1}\bigl(\dot r^a + \gamma\,\dot P^a V^a\bigr),$$
--   where $\dot r^a(i) = \alpha(i,a_i)\sigma^2(i,a_i)$ and $\dot P^a(i,j) = P^a(i,j)\beta(i,a_i,j)$ are the derivatives of the mean-reward vector and the transition matrix, $a_i$ denoting the action the arm-$a$ policy executes at $i$.
--
--   This is the standard sensitivity formula for a discounted Markov decision process, obtained by differentiating $V^a_t = (I - \gamma P^a_t)^{-1} r^a_t$: the transition matrix and the mean-reward vector are affine in $t$, and the matrix inverse is differentiable at an invertible point with derivative $-A^{-1}\dot A A^{-1}$, which combines with the product rule to the displayed expression. It is the term that turns a perturbation of the model into a perturbation of the average treatment effect, and hence the first half of the Cramér-Rao computation for Theorem 5.
--
--   *Formalization note.* The perturbed transition law is defined with a fallback outside the admissible range of $t$; differentiability at $0$ is unaffected because the two agree on a neighbourhood of $0$.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, Section 2 (V = (I - gamma P)^{-1} r) and Appendix EC.4 (the derivative of the ATE along the SST family, entering the constrained Cramer-Rao bound of Theorem 5). The sensitivity formula is classical; see M. L. Puterman, Markov Decision Processes, Wiley 1994, Chapter 6.

import Definitions.Def_TreatmentLocalityPerturbation
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.hasDerivAt_perturbModel_value {S : Type*} [DecidableEq S]
    [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (hgauss : M.GaussianRewards m v) (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (a : Bool) (s : S) :
    HasDerivAt (fun t : ℝ => (perturbModel M m v α β t).value a s)
      ((((1 : Matrix S S ℝ) - M.γdisc • M.polTrans a)⁻¹).mulVec
        (fun i => α i (M.act a i) * (v i (M.act a i) : ℝ)
          + M.γdisc * ∑ j, M.polTrans a i j * β i (M.act a i) j * M.value a j) s) 0 := by sorry
