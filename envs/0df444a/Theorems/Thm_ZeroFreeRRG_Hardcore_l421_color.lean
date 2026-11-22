-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_l421_color
-- name    : ZeroFreeRRG.Hardcore.l421_color
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:13:46.940795+00:00
-- url     : https://prove2.me/theorems/a88aab0f-960e-4b40-8522-9e8c863637c5
-- title:
--   Lemma 4.21, Step 3: quantitative cutoff uniformity at the coloring endpoint
-- statement:
--   For $q\ge2$, consider the $q$-state Potts model at the coloring endpoint $t=0$ and assume Conditions 1 and 2 there. For every sufficiently small overlap box $B$ about $U_q\otimes U_q$, there are a positive comparison parameter $0<x<1$, a cutoff $\varepsilon>0$, and constants $c,k>0$ with $2k<c$ such that the real truncation bound holds at $x$ with decay $e^{-cn}$ and the complex-versus-positive weight comparison about $0$ holds with loss $Ae^{kn}$.
--
--   Step 3 of Appendix E.4 obtains $c(x)\ge c_2(1+\log(1/x))^{-6}$, while the endpoint weight-perturbation cost is $O(xn)$. Since $c_2(1+\log(1/x))^{-6}\gg x$ as $x\downarrow0$, a fixed sufficiently small $x$ makes the real decay dominate the perturbation.
--
--   **Formalization Note.** This uses the same statement as `lemma_4_21_step3_coloring`, with a short identifier for the import resolver.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), Appendix E.4, Steps 3–4, p. 83 (printed), especially $c(x)\ge c_2(1+\log(1/x))^{-6}$ and the endpoint weight comparison.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Truncation

open scoped Classical

open AFIsingKS
open ZeroFreeRRG.Hardcore

/-- **Lemma 4.21, Step 3** (Appendix E.4, p. 83). At the proper-coloring endpoint, one can choose
a positive Potts comparison parameter whose real truncation decay dominates the complex
weight-perturbation cost. -/
theorem ZeroFreeRRG.Hardcore.l421_color
    (q : ℕ) (hq : 2 ≤ q) (d : ℕ) (hd : 3 ≤ d)
    (hC1 : Condition1 (.potts q) d 0) (hC2 : Condition2 (.potts q) d 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ (c₀ : Fin q × Fin q) (lo hi : Fin q × Fin q → ℝ),
      tensorVec ((Model.potts q).pi 0) ((Model.potts q).pi 0) ∈ overlapBox c₀ lo hi →
      (∀ ab, hi ab - lo ab < r) →
      ∃ x : ℝ, 0 < x ∧ x < 1 ∧ ∃ ε : ℝ, 0 < ε ∧
        (∀ n, IsGraphEvent (partitionCutoff (.potts q) x d n ε)) ∧
        ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ N : ℕ, ∃ A k R : ℝ, 2 * k < c ∧
          RealTruncationBound (.potts q) d x (overlapBox c₀ lo hi)
            (fun n => partitionCutoff (.potts q) x d n ε) c C N ∧
          WeightComparison (.potts q) d 0 x (overlapBox c₀ lo hi) A k R := by sorry
