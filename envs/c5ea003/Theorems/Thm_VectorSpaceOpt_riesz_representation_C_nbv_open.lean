-- Prove2me | Theorems.Thm_VectorSpaceOpt_riesz_representation_C_nbv_open
-- name    : VectorSpaceOpt.riesz_representation_C_nbv_open
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T03:16:44.258963+00:00
-- url     : https://prove2.me/theorems/e17caeaf-f022-40e6-a410-fe6d253b4c07
-- title:
--   Riesz representation theorem for $C[a,b]$
-- statement:
--   Let $f$ be a bounded linear functional on $X=C[a,b]$, the continuous real functions on $[a,b]$ under the supremum norm, with $a<b$. Then there is a function $v$ of bounded variation on $[a,b]$ such that $f$ is integration against $v$,
--
--   $$f(x)=\int_a^b x(t)\,dv(t)\qquad\text{for all }x\in X,$$
--
--   the integral being a Riemann–Stieltjes integral, and the norm of $f$ equals the total variation of $v$:
--
--   $$\|f\|=\mathrm{T.V.}(v).$$
--
--   The representative is taken in the **normalized** space $NBV[a,b]$ in Luenberger's sense: of bounded variation, vanishing at $a$, and continuous from the right at every point of the *open* interval $(a,b)$. Normalization is what makes the representative unique — without it, altering $v$ at an interior discontinuity changes nothing that a continuous integrand can detect.
--
--   The classical proof extends $f$ by Hahn–Banach from $C[a,b]$ to the space of all bounded functions on $[a,b]$ with the supremum norm, preserving the norm; the extension $F$ is then evaluated on indicators, $v(t)=F(\chi_{(a,t]})$, which gives $v(a)=0$ and $\mathrm{T.V.}(v)\le\|F\|=\|f\|$ by testing $F$ against $\sum_i\varepsilon_i\chi_{(t_{i-1},t_i]}$ with signs $\varepsilon_i=\pm1$, a function of supremum norm $1$. Approximating a continuous $x$ in supremum norm by the step functions $x(a)\chi_{\{a\}}+\sum_i x(t_i)\chi_{(t_{i-1},t_i]}$ identifies $F(x)=f(x)$ with the Riemann–Stieltjes integral, and the reverse inequality $\|f\|\le\mathrm{T.V.}(v)$ then follows from the elementary bound $\bigl|\int_a^b x\,dv\bigr|\le\|x\|\cdot\mathrm{T.V.}(v)$.
--
--   Together with the converse — every function of bounded variation defines such a functional — this identifies the dual of $C[a,b]$ concretely, which is what turns optimization problems posed on $C[a,b]$ into problems about functions of bounded variation.
--
--   **Formalization note.** The right-continuity requirement is imposed on the open interval $(a,b)$, which is Luenberger's definition. Imposing it at the left endpoint $a$ as well would make the statement false: with $v(a)=0$ and $v(a^+)=0$ the first cell of any tagged partition contributes $x(\xi_0)(v(t_1)-v(a))\to 0$, so a normalized $v$ could carry no atom at $a$, and the norm-one functional $x\mapsto x(a)$ would have no representative. The hypothesis $a<b$ excludes the degenerate interval, where every $v$ has zero total variation on the singleton $\{a\}$ while $C(\{a\},\mathbb{R})\cong\mathbb{R}$ still carries functionals of norm $1$.
-- source:
--   D. G. Luenberger, Optimization by Vector Space Methods, Wiley 1969, §5.5, pp. 113-115 (Riesz representation for C[a,b]); the Riemann-Stieltjes facts are the standard ones, e.g. T. M. Apostol, Mathematical Analysis, 2nd ed., Ch. 7, Theorems 7.19 and 7.27.

import Mathlib
import Definitions.Def_VectorSpaceOpt_is_nbv_open

namespace VectorSpaceOpt

theorem riesz_representation_C_nbv_open (a b : ℝ) (hab : a < b)
    (f : C(Set.Icc a b, ℝ) →L[ℝ] ℝ) :
    ∃ v : ℝ → ℝ, VectorSpaceOpt_is_nbv_open a b v ∧
      (∀ x : C(Set.Icc a b, ℝ),
        VectorSpaceOpt_is_rs_integral (Set.IccExtend (le_of_lt hab) x) v a b (f x)) ∧
      ‖f‖ = VectorSpaceOpt_total_variation v a b := by sorry

end VectorSpaceOpt
