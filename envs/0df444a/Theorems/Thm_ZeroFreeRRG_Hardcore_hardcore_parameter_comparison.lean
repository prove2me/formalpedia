-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_parameter_comparison
-- name    : ZeroFreeRRG.Hardcore.hardcore_parameter_comparison
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T03:56:01.2672+00:00
-- url     : https://prove2.me/theorems/065156bf-70a4-404c-b32e-0efe19587b21
-- title:
--   Strict hardcore Bethe comparison at lower occupation density
-- statement:
--   Let $d\ge3$ and $0<\alpha<\alpha'<1/2$. If the hardcore Bethe functional at $\alpha'$ is nonpositive on every cavity law with mean $(1-\alpha',\alpha')$, then at $\alpha$ it is strictly negative on every cavity law other than the point mass at its mean. It is also nonpositive on every cavity law at $\alpha$.
--
--   The result gives both the unique-maximizer condition and monotonicity of variational replica symmetry under decreasing occupation density.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510, proof of Lemma 4.17, pp. 29–31, especially equation (26) and the parameter comparisons; https://arxiv.org/abs/2610.40510

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical

namespace ZeroFreeRRG.Hardcore
/-- Strict Bethe comparison under decreasing hardcore occupation density,
Chen–Wang–Zhang (2026), proof of Lemma 4.17 pp. 30–31. -/
theorem hardcore_parameter_comparison (d : ℕ) (hd : 3 ≤ d) (α α' : ℝ)
    (hα : 0 < α) (hlt : α < α') (hα' : α' < 1 / 2)
    (hrs : VariationalRS .hardcore d α') :
    Condition1 .hardcore d α ∧ VariationalRS .hardcore d α := by sorry
end ZeroFreeRRG.Hardcore
