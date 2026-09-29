-- Prove2me | Theorems.Thm_ZudilinZeta_exists_saddle_root_params13
-- name    : ZudilinZeta.exists_saddle_root_params13
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-25T14:51:17.346154+00:00
-- url     : https://prove2.me/theorems/45d2ed84-894d-4be3-ac8e-4cda432e2396
-- title:
--   Existence of the saddle point $\tau_0$ for $r=3$, $q=13$ with the analytic hypotheses of Lemma 2
-- statement:
--   **Lemma 2 applied to the parameter set of the note.** For the parameters $r = 3$, $q = 13$, $\eta_0 = 91$, $\eta_1 = \eta_2 = \eta_3 = 27$, $\eta_4 = 29$, $\dots$, $\eta_{13} = 38$ of Zudilin's note, the saddle-point equation
--   $$(\tau-\eta_0)^3(\tau-\eta_1)\cdots(\tau-\eta_{13}) = \tau^3(\tau-\eta_0+\eta_1)\cdots(\tau-\eta_0+\eta_{13})$$
--   has a root $\tau_0$ in the upper half-plane $\operatorname{Im}\tau_0 > 0$, of maximal real part among the roots in the upper half-plane, with $\operatorname{Re}\tau_0 < \eta_0$, and such that $\operatorname{Im} f_0(\tau_0) \notin \pi\mathbb{Z}$, where $f_0$ is the auxiliary function of the note. These are exactly the hypotheses under which Lemma 2 of the note yields the asymptotic rate $\limsup_{n\to\infty} \log|F_n|/n = \operatorname{Re} f_0(\tau_0) = -C_0$, and under which the leading asymptotic coefficient of $|F_n|$ does not vanish ($F_n \neq 0$ for all large $n$). The companion node `ZudilinZeta.zudilin_numeric_C0_gt_C1` records the computed value $C_0 = 227.58019641\ldots$ for this root. The statement is the analytic-existence content of Lemma 2 specialised to the tuple (3, 13); it is faithful to the note and its follow-up paper (Zudilin, Izv. Ross. Akad. Nauk Ser. Mat. 66 (2002) 489–542), where the analogous saddle point is exhibited.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776), Lemma 2, and W. V. Zudilin, Irrationality of values of the Riemann zeta function, Izv. Math. 66:3 (2002), 489–542.

import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13

namespace ZudilinZeta
theorem exists_saddle_root_params13 :
    ∃ τ₀ : ℂ, charPoly params13 τ₀ = 0 ∧ 0 < τ₀.im ∧
      (∀ τ : ℂ, charPoly params13 τ = 0 → 0 < τ.im → τ.re ≤ τ₀.re) ∧
      τ₀.re < (params13.eta 0 : ℝ) ∧
      (∀ k : ℤ, (f0 params13 τ₀).im ≠ (k : ℝ) * Real.pi) := by sorry
end ZudilinZeta
