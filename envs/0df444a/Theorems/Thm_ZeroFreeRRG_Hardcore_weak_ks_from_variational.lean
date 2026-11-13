-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_weak_ks_from_variational
-- name    : ZeroFreeRRG.Hardcore.weak_ks_from_variational
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T03:55:51.222114+00:00
-- url     : https://prove2.me/theorems/8de22a15-0d9a-4b8a-8ce8-416998640041
-- title:
--   Variational replica symmetry implies the weak Kesten–Stigum bound
-- statement:
--   Let $d\ge3$ and $q\ge2$. In the hardcore model, if $0<\alpha<1/2$ and the Bethe functional is nonpositive on all cavity laws with mean $(1-\alpha,\alpha)$, then
--
--   $$ (d-1)\left(\frac{\alpha}{1-\alpha}\right)^2\le1. $$
--
--   In the antiferromagnetic $q$-state Potts model, if $0\le\beta<1$ and the corresponding Bethe functional is nonpositive on all cavity laws with uniform mean, then
--
--   $$ (d-1)\left(\frac{1-\beta}{q-1+\beta}\right)^2\le1. $$
--
--   These weak inequalities supply the stability bound at the stronger parameter in Lemma 4.17. The Potts interval includes the coloring endpoint $\beta=0$.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510, proof of Lemma 4.17, pp. 29–31, especially equation (26) and the parameter comparisons; https://arxiv.org/abs/2610.40510

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical

namespace ZeroFreeRRG.Hardcore
/-- The weak Kesten–Stigum condition from the fourth-order symmetric cavity perturbation,
Chen–Wang–Zhang (2026), proof of Lemma 4.17, equation (26). -/
theorem weak_ks_from_variational (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) :
    (∀ α : ℝ, 0 < α → α < 1 / 2 → VariationalRS .hardcore d α →
       ((d : ℝ) - 1) * (α / (1 - α)) ^ 2 ≤ 1) ∧
    (∀ β : ℝ, 0 ≤ β → β < 1 → VariationalRS (.potts q) d β →
       ((d : ℝ) - 1) * ((1 - β) / ((q : ℝ) - 1 + β)) ^ 2 ≤ 1) := by sorry
end ZeroFreeRRG.Hardcore
