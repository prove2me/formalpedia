-- Prove2me | Theorems.Thm_XuMannorRobust_WeakRobust_theorem8_generalizes_iff_weakly_robust
-- name    : XuMannorRobust.WeakRobust.theorem8_generalizes_iff_weakly_robust
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T16:04:49.735302+00:00
-- url     : https://prove2.me/theorems/d558229b-e3ea-4cdd-bddb-f0a5127a16b4
-- title:
--   Theorem 8 — a learning method generalizes w.r.t. $\mathbf s^*$ iff it is weakly robust w.r.t. $\mathbf s^*$
-- statement:
--   Let $\mathcal Z$ be a measurable space of samples with a probability measure $\mu$, $\mathcal H$ a set of hypotheses, and $l : \mathcal H \times \mathcal Z \to [0, M]$ a loss that is non-negative, bounded by $M$ and measurable in its sample argument. Let $\mathcal A = \{\mathcal A^n\}_{n \in \mathbb N}$, $\mathcal A^n : \mathcal Z^n \to \mathcal H$, be a learning method, and fix a sequence of training samples $\mathbf s^* = (s^*_1, s^*_2, \dots)$. Then
--
--   $$\mathcal A \text{ generalizes w.r.t. } \mathbf s^* \iff \mathcal A \text{ is weakly robust w.r.t. } \mathbf s^*,$$
--
--   that is, $\lim_n |\mathcal L(\mathcal A_{\mathbf s^*(n)}) - L(\mathcal A_{\mathbf s^*(n)}, \mathbf s^*(n))| = 0$ if and only if there are sets $\mathcal D_n \subseteq \mathcal Z^n$ with $\Pr_{\mathbf t(n) \sim \mu^n}(\mathbf t(n) \in \mathcal D_n) \to 1$ on which the average loss of $\mathcal A_{\mathbf s^*(n)}$ is uniformly within $o(1)$ of its training average loss.
--
--   The theorem says that a (weak) form of robustness is not only sufficient but also necessary for generalization: this is the sense in which Xu and Mannor call robustness an essential property of successful learning.
--
--   **Formalization Note** The training sequence is fixed and deterministic; all probabilities are over the test sample $\mathbf t(n) \sim \mu^n$, the product measure `Measure.pi (fun _ : Fin n => μ)`. The standing assumption of the paper (Sect. 1.1) that $0 \le l \le M$ is a hypothesis; measurability of $l(h, \cdot)$, which the paper ignores, is added. See the definitions for the encoding of Eq. (6).
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 409, Theorem 8

import Mathlib
import Definitions.Def_XuMannorRobust_WeakRobust_Generalizes
import Definitions.Def_XuMannorRobust_WeakRobust_WeaklyRobust

open MeasureTheory

namespace XuMannorRobust.WeakRobust

/-- Xu & Mannor 2012, p. 409, Theorem 8: fix a sequence of training samples `s*`. A learning
method `A` generalizes w.r.t. `s*` if and only if it is weakly robust w.r.t. `s*` (samples i.i.d.
from the probability measure `μ`; loss measurable with values in `[0, M]`). -/
theorem theorem8_generalizes_iff_weakly_robust {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    (A : (n : ℕ) → (Fin n → Z) → H) (sStar : ℕ → Z) :
    Generalizes μ l A sStar ↔ WeaklyRobust μ l A sStar := by sorry

end XuMannorRobust.WeakRobust
