-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_27
-- name    : ZeroFreeRRG.Hardcore.lemma_4_27
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:56:02.463952+00:00
-- url     : https://prove2.me/theorems/d6c22a99-7d28-4f97-af62-57b344b233db
-- title:
--   Coloring Bethe convexity and strict conditions from degree slack
-- statement:
--   Fix integers $d,q\ge3$ and consider the proper $q$-coloring model. If some real $r>d$ satisfies $\mathcal B_{r,0}(\nu)\le0$ for every admissible cavity law $\nu$, then the strict variational Condition 1 and strict Kesten–Stigum Condition 2 hold at degree $d$.
--
--   Moreover, nonpositivity for every admissible law is preserved as the interpolated degree decreases through nonnegative values. For each nonconstant admissible cavity law $\nu$, the function $s\mapsto\mathcal B_{s,0}(\nu)$ is convex on $[0,\infty)$, with
--
--   $$\mathcal B_{0,0}(\nu)=0,\qquad \mathcal B_{1,0}(\nu)<0.$$
--
--   This connects the coloring threshold's real-degree slack to the hypotheses of the paper's zero-freeness theorem.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Lemma 4.27, printed pp. 34–35.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical

namespace ZeroFreeRRG.Hardcore

/-- Lemma 4.27: real-degree slack yields strict coloring conditions, and degree convexity. -/
theorem lemma_4_27 (d q : ℕ) (hd : 3 ≤ d) (hq : 3 ≤ q) :
    ((∃ r : ℝ, (d : ℝ) < r ∧
      ∀ ν ∈ cavityLaws (.potts q) 0, betheR (.potts q) 0 r ν ≤ 0) →
      Condition1 (.potts q) d 0 ∧ Condition2 (.potts q) d 0) ∧
    (∀ r s : ℝ, 0 ≤ s → s ≤ r →
      (∀ ν ∈ cavityLaws (.potts q) 0, betheR (.potts q) 0 r ν ≤ 0) →
      ∀ ν ∈ cavityLaws (.potts q) 0, betheR (.potts q) 0 s ν ≤ 0) ∧
    (∀ ν ∈ cavityLaws (.potts q) 0, ν ≠ diracPi (.potts q) 0 →
      ConvexOn ℝ (Set.Ici 0) (fun s => betheR (.potts q) 0 s ν) ∧
      betheR (.potts q) 0 0 ν = 0 ∧ betheR (.potts q) 0 1 ν < 0) := by sorry
end ZeroFreeRRG.Hardcore
