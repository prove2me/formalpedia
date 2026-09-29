-- Prove2me | Theorems.Thm_mme_dwz_q5_target_count_log_rate
-- name    : mme_dwz_q5_target_count_log_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T13:44:13.243653+00:00
-- url     : https://prove2.me/theorems/47a90c96-3364-4a35-b1ec-136f661cf4c0
-- title:
--   Exact q=5 target-family logarithmic growth on synchronized lengths
-- statement:
--   Use the original rational-replay $q=5$ fourth-power data and the synchronized integer counts defined in `mme_dwz_q5_global_asymptotic_data`. Put $a_c=n_c(1)$ and $A=N(1)=\sum_c a_c$. Then $A>0$, and for every integer $t\ge0$,
--   $$
--   n_c(t)=t a_c,\qquad N(t)=tA.
--   $$
--   In particular, these permitted lengths tend to infinity. For the exact number of target words
--   $$
--   T(t)=\frac{N(t)!}{\prod_c n_c(t)!},\qquad
--   H_T=\frac{A\log A-\sum_c a_c\log a_c}{A},
--   $$
--   the normalized natural logarithm satisfies
--   $$
--   \lim_{t\to\infty}\frac{\log T(t)}{N(t)}=H_T.
--   $$
--   Consequently, for every real $h<H_T$, all sufficiently large $t$ satisfy $e^{hN(t)}\le T(t)$. This supplies the actual target-family count rate on the same denominator-cleared length sequence used by the finite tensor extraction. It asserts neither a compatible-competitor bound nor the final DWZ surplus.
-- source:
--   Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5, Sections 3.7 and 6.2, the multinomial target-count estimate N_alpha = 2^(n H(alpha)+o(n)); natural-log form for the unchanged exact rational-replay q=5 profiles. Uses the public scaled multinomial log-rate theorem.

import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Mathlib.Topology.Algebra.Order.Field

open Filter MME.DWZQ5AsymptoticData
open scoped Topology
set_option autoImplicit false

theorem mme_dwz_q5_target_count_log_rate :
    (∀ (t : ℕ) (c : Fin 45), n t c = n 1 c * t) ∧
    0 < N 1 ∧
    (∀ t : ℕ, N t = N 1 * t) ∧
    Tendsto N atTop atTop ∧
    Tendsto (fun t : ℕ ↦ Real.log (targetCount t : ℝ) / (N t : ℝ))
      atTop (𝓝 targetRate) ∧
    ∀ a : ℝ, a < targetRate →
      ∀ᶠ t : ℕ in atTop, Real.exp (a * (N t : ℝ)) ≤ (targetCount t : ℝ) := by sorry
