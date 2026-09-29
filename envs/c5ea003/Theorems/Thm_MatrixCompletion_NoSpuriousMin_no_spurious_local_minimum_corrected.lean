-- Prove2me | Theorems.Thm_MatrixCompletion_NoSpuriousMin_no_spurious_local_minimum_corrected
-- name    : MatrixCompletion.NoSpuriousMin.no_spurious_local_minimum_corrected
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-14T18:52:43.879415+00:00
-- url     : https://prove2.me/theorems/ae3cc320-db7b-4ff6-b6bf-19f3f943c517
-- title:
--   Matrix completion has no spurious local minimum (GLM Thm 5.3 / Chen–Li Cor 2.2, corrected sampling constant)
-- statement:
--   **Matrix completion has no spurious local minimum** (Ge–Lee–Ma Theorem 5.3 in Chen–Li's Corollary 2.2 form), with a sampling constant the proof can actually use.
--
--   Let $M=ZZ^\top$ with $Z\in\mathbb R^{d\times r}$ $\mu$-incoherent (Ge–Lee–Ma Assumption 1), $\|Z\|_F^2=r$, $\sigma_{\max}(Z)\le\kappa\,\sigma_{\min}(Z)$ and $\sigma_{\min}(Z)>0$. Tune data-adaptively inside Chen–Li's windows, $100\|Z\|_{2\to\infty}\le\alpha\le200\|Z\|_{2\to\infty}$ and $100\|\Omega-pJ\|\le\lambda\le200\|\Omega-pJ\|$, and let $\Omega$ be a good sample. If the sampling rate satisfies
--
--   $$p\;\ge\;\frac{10^{28}\,\mu^4\kappa^4r^2\,(1+\log d)}{d},$$
--
--   then every local minimum $X$ of the regularized objective
--
--   $$f(X)=\tfrac12\bigl\|P_\Omega(M-XX^\top)\bigr\|_F^2+\lambda\sum_{i=1}^d\bigl(\|X_i\|-\alpha\bigr)_+^4$$
--
--   is a global minimum: $f(X)=0$ and $XX^\top=ZZ^\top$. Non-convexity notwithstanding, the landscape hides no traps, which is why gradient descent from an arbitrary initialization provably solves positive semidefinite matrix completion.
--
--   **Relation to the mission's goal theorem.** This is the mission's `no_spurious_local_minimum` (`45993f97-a08e-45fe-8944-932c4d74532f`) with one extra hypothesis: the sampling rate is required with the constant $10^{28}$ in place of the $10^{10}$ hard-coded in the `SampleCondition` definition, and $\log d$ is replaced by $1+\log d$ so that the hypothesis also bites at small $d$. Everything else — the statement, the model layer, the good-sample predicate — is unchanged, so this theorem is strictly weaker and implies nothing the original does not.
--
--   The strengthening is not cosmetic. The Chen–Li route reaches the goal through `perturbation_terms_bound` and `K_superlevel_bound`, and both of those are **false** at the $10^{10}$ instantiation: explicit machine-checked counterexamples are recorded on the platform (disproofs `a797f42a-1928-4b1b-90ab-2234a526d06e` and `ac265185-c5b6-4443-867c-a3b32ea9049b`). Balancing the regularizer's $\lambda\alpha^2\|\Delta\|_F^2$ against the $\tfrac{p}{1000}\sigma_{\min}(Z)^2\|\Delta\|_F^2$ that the target offers requires $pd\gtrsim10^{27}\mu^4r^2\kappa^4$, whereas `SampleCondition` supplies only $pd\ge10^{10}\mu^4\kappa^4r^2\log d$. Chen–Li state their Lemma 4.8 "for a sufficiently large absolute constant $C$"; $10^{28}$ is large enough. It forces $d\gtrsim10^{29}$ before the hypothesis is satisfiable at all, which is the asymptotic regime the statement was always about.
--
--   **Formalization note.** This is the deterministic core of the high-probability statement: the randomness of $\Omega$ factors through the good-sample predicate (Chen–Li Lemmas 4.1–4.2), whose probabilistic verification is a separate matter. Local minimality is Lean's topological `IsLocalMin` on $\mathbb R^{d\times r}$.
-- source:
--   Chen, Li 2019, Model-free Nonconvex Matrix Completion, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3), p. 8, Corollary 2.2 (exact recovery at every local minimum; deterministic core), with the absolute constant C of Lemma 4.8 instantiated at 10^28 rather than 10^10.  Provenance: Ge, Lee, Ma 2016, Matrix Completion has No Spurious Local Minimum, https://arxiv.org/abs/1605.07272 (v4), p. 11, Theorem 5.3; improves Ge, Jin, Zheng 2017, https://arxiv.org/abs/1704.00708, Theorem 12.

import Definitions.Def_MCNoSpuriousMinModel
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Matrix MatrixCompletion.NoSpuriousMin

theorem MatrixCompletion.NoSpuriousMin.no_spurious_local_minimum_corrected
    {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r)
    (Z X : Matrix (Fin d) (Fin r) ℝ) (Ω : Finset (Fin d × Fin d))
    (p μ κ lam α : ℝ)
    (hμ : 1 ≤ μ) (hκ : 1 ≤ κ) (hcond : sigmaMax Z ≤ κ * sigmaMin Z)
    (hσ : 0 < sigmaMin Z)
    (hinc : Incoherent μ Z) (hZnorm : frobSq Z = (r : ℝ))
    (hα1 : 100 * twoInftyNorm Z ≤ α) (hα2 : α ≤ 200 * twoInftyNorm Z)
    (hlam1 : 100 * sampDevNorm Ω p ≤ lam) (hlam2 : lam ≤ 200 * sampDevNorm Ω p)
    (hp : SampleCondition d r p μ κ)
    (hpC : 10 ^ 28 * μ ^ 4 * κ ^ 4 * (r : ℝ) ^ 2 * (1 + Real.log d) / d ≤ p)
    (hgood : GoodSample Z Ω p)
    (hmin : IsLocalMin (objective Z Ω lam α) X) :
    objective Z Ω lam α X = 0 ∧ X * Xᵀ = Z * Zᵀ := by sorry
