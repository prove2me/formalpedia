-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_hardcore_interior_conditions
-- name    : ZeroFreeRRG.Hardcore.hardcore_interior_conditions
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:09:54.162195+00:00
-- url     : https://prove2.me/theorems/e3964d3e-abab-40bd-8217-6e3e99ee0e81
-- title:
--   Hardcore interior implies both strict conditions
-- statement:
--   Fix $d\ge3$ and a hardcore parameter $\alpha\in(0,1/2)$ in the interior of the variational replica-symmetric regime. Then both the strict Bethe Condition 1 and the strict Kesten–Stigum Condition 2 hold at $(d,\alpha)$.
--
--   This is the hardcore strict-conditions branch of Lemma 4.17; it isolates the part needed for the hardcore zero-free region.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Lemma 4.17, printed pp. 29–30, hardcore branch.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical

namespace ZeroFreeRRG.Hardcore
/-- The hardcore strict-conditions branch of Lemma 4.17. -/
theorem hardcore_interior_conditions (d : ℕ) (hd : 3 ≤ d) (α : ℝ)
    (hα : 0 < α) (hα2 : α < 1/2) (hint : InteriorVariationalRS .hardcore d α) :
    Condition1 .hardcore d α ∧ Condition2 .hardcore d α := by sorry
end ZeroFreeRRG.Hardcore
