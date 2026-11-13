-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_potts_edge_nonconstant
-- name    : ZeroFreeRRG.Hardcore.potts_edge_nonconstant
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:51:21.024194+00:00
-- url     : https://prove2.me/theorems/2ed9f8ec-0932-4e3c-9e7c-d80c2180b0ee
-- title:
--   A nontrivial Potts cavity law has a nonconstant edge factor
-- statement:
--   Let $q\ge2$ and $0\le\beta<1$. Suppose $\nu$ is a Potts cavity law, supported on the probability simplex with uniform barycenter, and is not the point mass at the uniform message. For two independent messages $X,Y\sim\nu$, their edge factor $E_\beta(X,Y)$ is nonnegative and differs from $1$ with positive probability. This is the strictness input in the Potts Bethe-functional comparison.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.17, printed pp. 30–31.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem potts_edge_nonconstant (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hb0 : 0 ≤ β) (hb1 : β < 1)
    (ν : ProbabilityMeasure (Fin q → ℝ)) (hν : ν ∈ cavityLaws (.potts q) β)
    (hne : ν ≠ diracPi (.potts q) β) :
    0 < ((ν : Measure (Fin q → ℝ)).prod (ν : Measure (Fin q → ℝ)))
      {p | 0 ≤ edgeFactor (.potts q) β p.1 p.2 ∧ edgeFactor (.potts q) β p.1 p.2 ≠ 1} := by sorry
end ZeroFreeRRG.Hardcore
