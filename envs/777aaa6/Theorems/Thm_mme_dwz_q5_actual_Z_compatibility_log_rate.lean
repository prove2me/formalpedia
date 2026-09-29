-- Prove2me | Theorems.Thm_mme_dwz_q5_actual_Z_compatibility_log_rate
-- name    : mme_dwz_q5_actual_Z_compatibility_log_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T14:03:59.487669+00:00
-- url     : https://prove2.me/theorems/c1b6faca-9383-413f-971e-32cde1542904
-- title:
--   Exact logarithmic rate of the original q=5 fine-Z compatibility count
-- statement:
--   Use the unchanged public rational-replay $q=5$ fourth-power profiles and the exact B1 counting family. Let $D$ be the product of their denominators, let $n_c(t)$ and $\mu_{c,l}(t)$ be the synchronized component and Z-split counts, and put $N(t)=\sum_c n_c(t)$. These are the same profiles and integer counts used in the accepted exact counting construction, with no averaging or retuning.
--
--   Write $F_i(t)$ for the total-grade/left-tag histogram, and $q_{d,i}(t)$ for the pooled histogram: each boundary component remains separate, while nonboundary components are pooled only by their Z grade. The accepted B1 compatible-owner count is
--   $$
--   W(t)=
--   \left(\prod_i\frac{F_i(t)!}{\prod_d q_{d,i}(t)!}\right)
--   \left(\prod_d\frac{\left(\sum_iq_{d,i}(t)\right)!}
--   {\prod_{c:\chi(c)=d}n_c(t)!}\right).
--   $$
--   Set $S=N(1)$ and $A_d=\sum_iq_{d,i}(1)$. Define the explicit natural-log rate
--   $$
--   L_Z=\frac{1}{S}
--   \left[
--   \sum_iF_i(1)\log F_i(1)
--   -\sum_{d,i}q_{d,i}(1)\log q_{d,i}(1)
--   +\sum_d A_d\log A_d
--   -\sum_c n_c(1)\log n_c(1)
--   \right].
--   $$
--   Here $0\log0=0$. Then $W(t)>0$ for every nonnegative integer $t$, and
--   $$
--   \lim_{t\to\infty}\frac{\log W(t)}{N(t)}=L_Z.
--   $$
--   Moreover, for every real $a>L_Z$, all sufficiently large $t$ satisfy
--   $$
--   W(t)\le \exp(aN(t)),
--   \qquad
--   W(t)-1\le \exp(aN(t)).
--   $$
--
--   Thus the actual excluded-owner compatibility count supplied by B1 has this eventual exponential upper bound. The logarithmic limit is derived from exact multinomial asymptotics; it is not an assumed entropy estimate. Zero pooled rows are included. The theorem does not claim a logarithmic limit for $W(t)-1$ when that sequence can vanish, nor does it supply component tensor values or a matrix-multiplication exponent conclusion.
--
--   **Formalization Note.** The shared data constants are exactly the B1 factorial formula and synchronized raw parent profiles. The rate is compatibilityRate; the count and length are W and N.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5 , Section 3.6 Lemma 3.4 and Section 6.2 Lemma 6.7 / Claim 6.8. Derived exact natural-log limit for the original rational-replay q=5 candidate's B1 compatibility count, not a verbatim numbered paper statement. Uses the published q5_global_asymptotic_data and the accepted exact counting construction for power4_dup_2.371919.mat, https://osf.io/dta6p/files/zx3yf .

import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Mathlib.Topology.Algebra.Order.Field

open Filter
open scoped Topology Classical
set_option autoImplicit false

theorem mme_dwz_q5_actual_Z_compatibility_log_rate :
    (∀ t : ℕ, 0 < MME.DWZQ5AsymptoticData.W t) ∧
    Filter.Tendsto (fun t : ℕ ↦ Real.log (MME.DWZQ5AsymptoticData.W t : ℝ) /
      (MME.DWZQ5AsymptoticData.N t : ℝ)) Filter.atTop
      (nhds MME.DWZQ5AsymptoticData.compatibilityRate) ∧
    (∀ a : ℝ, MME.DWZQ5AsymptoticData.compatibilityRate < a →
      ∀ᶠ t : ℕ in Filter.atTop, (MME.DWZQ5AsymptoticData.W t : ℝ) ≤
        Real.exp (a * (MME.DWZQ5AsymptoticData.N t : ℝ))) ∧
    (∀ a : ℝ, MME.DWZQ5AsymptoticData.compatibilityRate < a →
      ∀ᶠ t : ℕ in Filter.atTop, ((MME.DWZQ5AsymptoticData.W t - 1 : ℕ) : ℝ) ≤
        Real.exp (a * (MME.DWZQ5AsymptoticData.N t : ℝ))) := by sorry
