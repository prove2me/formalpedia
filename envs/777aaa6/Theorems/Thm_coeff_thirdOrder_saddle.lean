-- Prove2me | Theorems.Thm_coeff_thirdOrder_saddle
-- name    : coeff_thirdOrder_saddle
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:51:41.602999+00:00
-- url     : https://prove2.me/theorems/0e61711d-0071-435b-bef9-00ad34fa471f
-- title:
--   Saddle coefficient ratio under explicit weighted local and uniform tail hypotheses
-- statement:
--   Let $p$ be the actual complex Taylor series of $f$ at zero. Supply an admissibility record with a nontrivial radial filter $F$, real functions $a,b,\delta$, eventual positive radius, $\operatorname{Re}f(r)>0$, $b(r)>0$, differentiability on the closed radius-$r$ disk, and $0<\delta(r)\le\pi$. Assume $\delta(r)\sqrt{b(r)}\to\infty$. The first-order uniform local condition says that, for every $\varepsilon>0$, eventually along $F$ all real $\theta$ with $|\theta|\le\delta(r)$ satisfy $|L(r,\theta)-1|\le\varepsilon$. The first-order tail condition supplies an eventually nonnegative $E_0(r)$ such that $\sqrt{2\pi b(r)}E_0(r)\to0$ and, eventually along $F$, $|G(r,n,\theta)|\le E_0(r)$ simultaneously for every natural $n$ and every real $\theta$ with $\delta(r)\le|\theta|\le\pi$. The functions $L,G$ are defined below. Supply a saddle sequence $r_n$ tending to $F$ with $a(r_n)=n$ eventually.
--
--   The functions $a,b,b_3,b_4,b_5,b_6,\delta,c_2,c_3$ are supplied real-valued functions of the radius; the general records do not separately identify them as logarithmic derivatives. Define
--
--   $$L(r,\theta)=\frac{f(re^{i\theta})e^{-ia(r)\theta}}{f(r)e^{-b(r)\theta^2/2}},\qquad G(r,n,\theta)=\frac{f(re^{i\theta})}{f(r)}e^{-in\theta}.$$
--
--   For the following formulas, all $b,b_j,s$ are evaluated at $r$, and $s=\sqrt{b(r)}$. The source's complex polynomials are
--
--   $$P_2(r,x)=1-\frac{i b_3x^3}{6s^3}+\frac{b_4x^4}{24b^2}-\frac{b_3^2x^6}{72b^3},$$
--
--   $$\begin{aligned}
--   P_3(r,x)={}&P_2(r,x)+\frac{i b_5x^5}{120s^5}-\frac{b_6x^6}{720b^3}
--   -\frac{i b_3b_4x^7}{144s^3b^2}\\
--   &+\frac{b_3b_5x^8}{720b^4}+\frac{b_4^2x^8}{1152b^4}
--   +\frac{i b_3^3x^9}{1296s^9}\\
--   &-\frac{b_3^2b_4x^{10}}{1728b^5}+\frac{b_3^4x^{12}}{31104b^6}.
--   \end{aligned}$$
--
--   The real absolute correction scales are
--
--   $$Q_2(r)=\frac{|b_4|}{b^2}+\frac{b_3^2}{b^3},$$
--   $$Q_3(r)=Q_2(r)+\frac{|b_6|}{b^3}+\frac{|b_3b_5|}{b^4}+\frac{b_4^2}{b^4}+\frac{b_3^2|b_4|}{b^5}+\frac{b_3^4}{b^6}.$$
--
--   For each $j=2,3$, the supplied scale $c_j(r)$ must be eventually positive, tend to zero, and satisfy $Q_j(r)\le K_jc_j(r)$ eventually for some fixed $K_j\ge0$. The carried local accuracy premise is
--
--   $$\frac{1}{c_j(r)}\int_{-\delta(r)\sqrt{b(r)}}^{\delta(r)\sqrt{b(r)}}\left|e^{-x^2/2}\left(L(r,x/\sqrt{b(r)})-P_j(r,x)\right)\right|\,dx\longrightarrow0.$$
--
--   The carried tail premise supplies an eventually nonnegative $E_j(r)$, uniformly bounding $|f(re^{i\theta})e^{-in\theta}/f(r)|$ for every natural $n$ and $\delta(r)\le|\theta|\le\pi$, with $\sqrt{2\pi b(r)}E_j(r)/c_j(r)\to0$. These accuracy conditions are hypotheses, not consequences of analyticity alone.
--
--   With $S_n=f(r_n)/(r_n^n\sqrt{2\pi b(r_n)})$, the conclusion is
--
--   $$\frac{p.\mathrm{coeff}(n)}{S_n}-\bigl(1+d_1(r_n)+d_2(r_n)\bigr)=o(c_3(r_n)).$$
--
--   The corrections are
--
--   $$d_1(r)=\frac{b_4(r)}{8b(r)^2}-\frac{5b_3(r)^2}{24b(r)^3},\qquad d_2(r)=-\frac{b_6(r)}{48b(r)^3}+\frac{7b_3(r)b_5(r)}{48b(r)^4}+\frac{35b_4(r)^2}{384b(r)^4}-\frac{35b_3(r)^2b_4(r)}{64b(r)^5}+\frac{385b_3(r)^4}{1152b(r)^6}.$$
--
--   The source does not require $c_3=o(c_2)$ or promise a strictly smaller remainder merely from the third-order name. It does not construct the records or saddle sequence from analyticity.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/ThirdOrderHAdmissible.lean#L1283. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderHAdmissible
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Third-order H-admissible wrapper

This is a clean add-on to the second-order `HAdmissible` interface.  It records
the fifth and sixth logarithmic saddle derivatives, the robust third-order
scale, and the local/tail hypotheses used by the third-order saddle layer.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

theorem coeff_thirdOrder_saddle
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      p.coeff n / saddleScale f hr.r (HAdmissible.B hf hr) n -
        (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
          (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by sorry
