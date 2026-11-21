-- Prove2me | Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
-- name    : moebius_summatory_rpow_bound_of_riemannHypothesis
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-20T22:58:15.165383+00:00
-- url     : https://prove2.me/theorems/465491a6-91e2-4ec8-b3c7-95f64438963d
-- title:
--   Littlewood: the Riemann hypothesis implies $M(N)=O(N^{1/2+\varepsilon})$
-- statement:
--   Let $\mu$ be the Möbius function and let
--
--   $$M(N)=\sum_{n=1}^{N}\mu(n)\qquad(N\in\mathbb N)$$
--
--   be the Mertens function. Assume the Riemann hypothesis in Mathlib's form: every zero $s$ of $\zeta$ with $s\neq 1$ that is not a trivial zero $-2,-4,-6,\dots$ satisfies $\operatorname{Re}s=\tfrac12$. Then for every real $\varepsilon>0$
--
--   $$M(N)=O_\varepsilon\!\left(N^{1/2+\varepsilon}\right)\qquad(N\to\infty).$$
--
--   That is, for each $\varepsilon>0$ there is a constant $C_\varepsilon$, independent of $N$, with $|M(N)|\le C_\varepsilon N^{1/2+\varepsilon}$ for all sufficiently large $N$.
--
--   This is the classical, unconditionally provable implication "RH $\Rightarrow$ Mertens bound" due to Littlewood (1912). It is the forward direction of the criterion in Titchmarsh–Heath-Brown, Theorem 14.25(C). It is a theorem, not a conjecture: the Riemann hypothesis is a hypothesis of the statement.
--
--   **Classical proof outline.** Under RH one has $\log\zeta(s)=O\big((\log t)^{2-2\sigma+\delta}\big)$ for $\tfrac12<\sigma\le1$ (Titchmarsh–Heath-Brown §14.2). Consequently
--
--   $$\frac{1}{\zeta(\sigma+it)}=O_{\delta,\varepsilon}\!\left(|t|^{\varepsilon}\right)$$
--
--   uniformly for $\sigma\ge\tfrac12+\delta$ and $|t|\ge1$. Apply the truncated Perron formula to $1/\zeta(w)=\sum_n\mu(n)n^{-w}$ on the line $\operatorname{Re}w=1+1/\log x$ with height $T$. Then move the contour to $\operatorname{Re}w=\tfrac12+\varepsilon$. No poles are crossed, because $1/\zeta$ is holomorphic for $\operatorname{Re}w>\tfrac12$ under RH. Bound the shifted integrals using the estimate above and choose $T=x$. The result is $M(x)=O(x^{1/2+2\varepsilon})$.
--
--   **Formalization Note.** The hypothesis is Mathlib's `RiemannHypothesis`. The conclusion is verbatim the statement of the platform theorem `moebius_summatory_rpow_bound`: the integer-valued partial sums are cast to $\mathbb C$, the comparison function is the real power $N^{1/2+\varepsilon}$, and `Asymptotics.IsBigO Filter.atTop` expresses the $O$-estimate along $N\to\infty$ in $\mathbb N$.
-- source:
--   J. E. Littlewood, Quelques conséquences de l'hypothèse que la fonction ζ(s) de Riemann n'a pas de zéros dans le demi-plan Re(s) > 1/2, C. R. Acad. Sci. Paris 154 (1912), 263–266. E. C. Titchmarsh, The Theory of the Riemann Zeta-function, 2nd ed., revised by D. R. Heath-Brown, Oxford University Press, 1986, §14.25, Theorem 14.25(C), equation (14.25.2), p. 370 (forward direction: RH implies (14.25.2)), using the conditional bounds for log ζ and 1/ζ of §14.2. https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

theorem moebius_summatory_rpow_bound_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)) := by sorry
