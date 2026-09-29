-- Prove2me | Theorems.Thm_siegel_logdensity_phi_deriv_pos
-- name    : siegel_logdensity_phi_deriv_pos
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T18:50:58.984319+00:00
-- url     : https://prove2.me/theorems/ca80b7e3-211c-47f2-b565-df1753598128
-- title:
--   Siegel Theorem 2.2: sign of $\varphi'$ for the waiting-time log-density
-- statement:
--   **Siegel 2001, "Median Bounds and their Application" (J. Algorithms 38:184–236), Theorem 2.2 / §2.1.1 — the $\varphi'$-sign step.**
--
--   For the waiting-time log-density $G(t) = m\log(1 - e^{-\lambda t}) - (N-m)\lambda t$ (this is $\log f(t)$ up to the additive constant $\log K$, where $f(t) = K(1-e^{-\lambda t})^m (e^{-\lambda t})^{N-m}$ is the Siegel exponential-clock waiting-time density), define the symmetrized log-ratio $\varphi(t) = G(t) - G(2\mu - t)$.
--
--   Under the small-mean condition $(N-m)e^{\lambda\mu} < N$ (equivalently $e^{\lambda\mu} < N/(N-m)$, which the mean $\mu = \mathbb{E}[T] = \tfrac1\lambda\sum_{j=N-m+1}^{N}\tfrac1j < \tfrac1\lambda\log\tfrac{N}{N-m}$ satisfies), the derivative $\varphi'(t) = G'(t) + G'(2\mu - t)$ is strictly positive for every $t \in (0,\mu)$, where $G'(s) = m\lambda e^{-\lambda s}/(1-e^{-\lambda s}) - (N-m)\lambda$.
--
--   The statement asserts both `HasDerivAt` (the chain-rule derivative formula for $\varphi$ at each interior $t$) and the strict positivity of that derivative value.
--
--   **Proof.** The chain rule on $\log$, $\exp$ gives `HasDerivAt`. For the sign, write $\alpha = e^{\lambda t}-1>0$, $\beta = e^{\lambda(2\mu-t)}-1>0$; then $\varphi'(t) = \lambda\,(m/\alpha + m/\beta - 2(N-m))$. Clearing the positive denominator $\alpha\beta$ and using $\alpha+\beta = e^{\lambda t}+e^{\lambda(2\mu-t)} - 2 \ge 2e^{\lambda\mu}-2$ (AM–GM, since $e^{\lambda t}\,e^{\lambda(2\mu-t)} = e^{2\lambda\mu}$) together with $\alpha\beta = e^{2\lambda\mu} - (e^{\lambda t}+e^{\lambda(2\mu-t)}) + 1$, the inequality reduces to the factorisation $(e^{\lambda\mu}-1)\big((N-m)e^{\lambda\mu} - N\big) < 0$, which holds because $e^{\lambda\mu}>1$ and $(N-m)e^{\lambda\mu}<N$. (The quadratic in $e^{\lambda t}$ governing the sign has negative discriminant under this condition, so $\varphi$ is in fact monotone increasing on $(0,\mu)$ — the degenerate single-turning-point case of Siegel's moustache argument.)
-- source:
--   Siegel, A. (2001). Median Bounds and their Application. Journal of Algorithms 38(1):184-236, Theorem 2.2 and §2.1.1 (waiting-time density / log-derivative sign analysis).

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
open Set

theorem siegel_logdensity_phi_deriv_pos
    (lam m Nn mu : ℝ)
    (hlam : 0 < lam) (hm : 0 < m) (hmN : m < Nn) (hmu : 0 < mu)
    (hcond : (Nn - m) * Real.exp (lam * mu) < Nn) :
    ∀ t ∈ Set.Ioo (0:ℝ) mu,
      HasDerivAt (fun y => (m * Real.log (1 - Real.exp (-lam * y)) - (Nn - m) * (lam * y))
                    - (m * Real.log (1 - Real.exp (-lam * (2*mu - y))) - (Nn - m) * (lam * (2*mu - y))))
        ( (m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)
          + (m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam) ) t
      ∧ 0 < ( (m * (lam * Real.exp (-lam * t) / (1 - Real.exp (-lam * t))) - (Nn - m) * lam)
          + (m * (lam * Real.exp (-lam * (2*mu - t)) / (1 - Real.exp (-lam * (2*mu - t)))) - (Nn - m) * lam) ) := by sorry
