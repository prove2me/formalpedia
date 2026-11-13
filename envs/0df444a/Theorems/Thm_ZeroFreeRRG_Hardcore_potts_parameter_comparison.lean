-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_parameter_comparison
-- name    : ZeroFreeRRG.Hardcore.potts_parameter_comparison
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T03:55:42.919049+00:00
-- url     : https://prove2.me/theorems/c650e667-31e6-4944-bf9f-768b9e374fef
-- title:
--   Strict Potts Bethe comparison at higher interaction parameter
-- statement:
--   Let $d\ge3$, $q\ge2$ and $0\le\beta'<\beta<1$. If the antiferromagnetic Potts Bethe functional at $\beta'$ is nonpositive on every cavity law with uniform mean, then at $\beta$ it is strictly negative on every cavity law other than the point mass at the uniform mean. It is also nonpositive on every cavity law at $\beta$.
--
--   The result gives the unique-maximizer condition and monotonicity of variational replica symmetry under increasing $\beta$. The starting parameter includes $\beta'=0$.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510, proof of Lemma 4.17, pp. 29–31, especially equation (26) and the parameter comparisons; https://arxiv.org/abs/2610.40510

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical

namespace ZeroFreeRRG.Hardcore
/-- Strict Bethe comparison under increasing antiferromagnetic Potts parameter,
Chen–Wang–Zhang (2026), proof of Lemma 4.17 pp. 30–31, including β'=0. -/
theorem potts_parameter_comparison (d q : ℕ) (hd : 3 ≤ d) (hq : 2 ≤ q) (β' β : ℝ)
    (hβ' : 0 ≤ β') (hlt : β' < β) (hβ : β < 1)
    (hrs : VariationalRS (.potts q) d β') :
    Condition1 (.potts q) d β ∧ VariationalRS (.potts q) d β := by sorry
end ZeroFreeRRG.Hardcore
