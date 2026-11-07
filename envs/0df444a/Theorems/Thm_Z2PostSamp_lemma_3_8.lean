-- Prove2me | Theorems.Thm_Z2PostSamp_lemma_3_8
-- name    : Z2PostSamp.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:07.614187+00:00
-- url     : https://prove2.me/theorems/2ae1c543-7dfe-4a7a-976e-3eb56b9357d5
-- title:
--   Lemma 3.8 — TAP gradient residual at the exact conditional mean: $\mathbb E\|\nabla_u\Phi_k(m^{(k)})\|^2\le C_\lambda(n-k)/n$
-- statement:
--   Fix $\lambda>1$. There is a constant $C_\lambda$ such that, for $\theta\sim\mu_J$ and the independent revealing order $I$, the target-prefix objective satisfies
--
--   $$\mathbb E\big\|\nabla_u\Phi_k\big(m^{(k)}(\theta_{S_k});\theta_{S_k}\big)\big\|^2\le C_\lambda\,\frac{n-k}n,\qquad k_0\le k<n .$$
--
--   The exact conditional mean is not a stationary point of the TAP objective, but its gradient residual is of order one per free coordinate fraction; with strong convexity this compares the constrained TAP minimizer with the true conditional mean.
--
--   **Formalization Note** The expectation is the lower Lebesgue integral under the planted law of $(\theta,Z,I)$, which gives $\theta\sim\mu_J$; $m^{(k)}$ is the conditional mean on $R_k$ and $\nabla_u\Phi_k$ the explicit gradient (zero off $R_k$).
--
--   Differences from the source:
--   - reading: θ ∼ μ_J and the independent revealing order I → the planted law of (θ, Z, I); reason: §2 preamble, p.5; Lemma 3.1
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), Lemma 3.8, p.29

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_Z2PostSamp_Model
import Definitions.Def_Z2PostSamp_RevealPath
import Definitions.Def_Z2PostSamp_Scalars
import Definitions.Def_Z2PostSamp_TAP
import Definitions.Def_Z2PostSamp_Construction

set_option autoImplicit false

open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Filter OAI.CriticalSK SKAnnealing.Sampling Matrix

namespace Z2PostSamp

/-- **Lemma 3.8 (TAP gradient residual).**
Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), Lemma 3.8, p.29: "For `θ ∼ μ_J` and the independent revealing order `I`, the target-prefix
objective satisfies `E‖∇_uΦ_k(m^{(k)}(θ_{S_k}); θ_{S_k})‖² ≤ C_λ (n − k)/n`, `k₀ ≤ k < n`."

**Formalization Note.** `λ > 1` is fixed (§3) and `C_λ` depends on `λ` only. The expectation is the
lower Lebesgue integral under the planted law of `(θ, Z, I)` (which gives `θ ∼ μ_J`), `m^{(k)}` the
exact conditional mean on `R_k` and `∇_uΦ_k` the gradient `tapGrad` (zero off `R_k`). -/
theorem lemma_3_8 (lam : ℝ) (hlam : 1 < lam) :
    ∃ C : ℝ, ∀ n k : ℕ, k0 n lam ≤ k → k < n →
      ∫⁻ ω, ENNReal.ofReal (sqNorm (tapGrad lam (Jof n lam ω) ω.2.2 ω.1 k
          (onR ω.2.2 k (condMean (Jof n lam ω) ω.2.2 ω.1 k)))) ∂(plantedLaw n)
        ≤ ENNReal.ofReal (C * ((n : ℝ) - k) / n) := by sorry

end Z2PostSamp
