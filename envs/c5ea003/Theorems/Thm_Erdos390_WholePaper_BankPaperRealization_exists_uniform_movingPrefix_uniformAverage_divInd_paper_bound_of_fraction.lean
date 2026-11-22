-- Prove2me | Theorems.Thm_Erdos390_WholePaper_BankPaperRealization_exists_uniform_movingPrefix_uniformAverage_divInd_paper_bound_of_fraction
-- name    : Erdos390.WholePaper.BankPaperRealization.exists_uniform_movingPrefix_uniformAverage_divInd_paper_bound_of_fraction
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:53:35.356383+00:00
-- url     : https://prove2.me/theorems/e3440aea-4f01-4d48-b89d-6fc7230f1d82
-- title:
--   Moving prefixes have sharp normalized Dickman divisibility profiles
-- statement:
--   Write $L_n=\log n$, $s_n=n/\log n$, $y_n=\lfloor n^{2/9}\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le y_n\}$. Fix a head pattern $P$, $0<A<C$, and $r_{\min}>0$. There exist $K>0,N_0$ such that whenever $n\ge N_0$, $\lfloor An\rfloor<k\le\lfloor Cn\rfloor$, and the physical prefix fraction is at least $r_{\min}$, the prefix cell $S=\operatorname{structuredCell}(P,\lfloor An\rfloor,k,y_n)$ is nonempty and
--   $$\left|\frac1{|S|}\sum_{m\in S}1_{d\mid m}-M_n(d)\right|\le\frac K{dL_n}.$$
--   This holds simultaneously for every integer $d>0$ with $d\le y_n^4$, all prime factors at most $y_n$, and $\gcd(d,P.\mathrm{modulus})=1$. The constant and threshold do not depend on the moving prefix or divisor. The physical prefix fraction means exactly $(k/n-A)/(C-A)$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/WholePaper/BankPaperCanonicalSmoothSourceGuardedSharpValuationRateClosureMoving.lean#L93-L254

import Definitions.Def_erdos390_remaining_analytic_propositions_007
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_005

theorem Erdos390.WholePaper.BankPaperRealization.exists_uniform_movingPrefix_uniformAverage_divInd_paper_bound_of_fraction : Erdos390.RemainingAnalyticGoal007_008 := by sorry
