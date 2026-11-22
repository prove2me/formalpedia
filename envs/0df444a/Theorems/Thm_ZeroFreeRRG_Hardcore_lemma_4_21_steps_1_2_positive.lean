-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_21_steps_1_2_positive
-- name    : ZeroFreeRRG.Hardcore.lemma_4_21_steps_1_2_positive
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T22:57:53.741809+00:00
-- url     : https://prove2.me/theorems/aca73a59-68a2-469b-ae0c-67a03ae29659
-- title:
--   Lemma 4.21, Steps 1–2: positive-parameter partition-function cutoff and real errors
-- statement:
--   Let $x$ be a positive nontrivial parameter for the hardcore model ($0<x<1/2$) or the antiferromagnetic Potts model ($0<x<1$), and assume Conditions 1 and 2 at $x$. For every sufficiently small overlap box $B$ about $\pi(x)\otimes\pi(x)$, there is $\varepsilon>0$ such that the cutoff event
--   $$E_n=\{G:\mathcal Z_G(x)\le a_n(x)e^{\varepsilon n}\}$$
--   has exponentially small real truncation errors. More precisely, the expected untruncated first moment on $E_n^{\mathrm c}$ is $O(e^{-cn}a_n(x))$, the expected in-box second moment on $E_n^{\mathrm c}$ is $O(e^{-cn}a_n(x)^2)$, and the out-of-box second moments both on $E_n$ and on $E_n^{\mathrm c}$ are $O(e^{-cn}a_n(x)^2)$ for some $c>0$.
--
--   This is the quantitative content of Steps 1–2 of Appendix E.4, including equation (76). The cutoff is a graph event because it depends only on the configuration-model multigraph.
--
--   **Formalization Note.** `RealTruncationBound` stores the four bounds with a common constant and threshold along admissible $n$ (with $dn$ even). At a positive parameter the summands are nonnegative, so the complex norms in the interface equal the corresponding real sums.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), Appendix E.4, Steps 1–2, pp. 82–83 (printed), equations (76)–(77).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Truncation

open scoped Classical

open AFIsingKS
open ZeroFreeRRG.Hardcore

/-- **Lemma 4.21, Steps 1–2** (Appendix E.4, pp. 82–83). At a positive parameter satisfying
Conditions 1 and 2, for every sufficiently small overlap box there is a cutoff level `ε > 0` such
that `E_n = {𝒵_G(x) ≤ a_n(x) exp(εn)}` is a graph event and all real truncation errors are
exponentially small. -/
theorem ZeroFreeRRG.Hardcore.lemma_4_21_steps_1_2_positive
    (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d)
    (x : ℝ) (hx : m.PosParam x) (hC1 : Condition1 m d x) (hC2 : Condition2 m d x) :
    ∃ r : ℝ, 0 < r ∧ ∀ (c₀ : m.Spin × m.Spin) (lo hi : m.Spin × m.Spin → ℝ),
      tensorVec (m.pi x) (m.pi x) ∈ overlapBox c₀ lo hi → (∀ ab, hi ab - lo ab < r) →
      ∃ ε : ℝ, 0 < ε ∧
        (∀ n, IsGraphEvent (partitionCutoff m x d n ε)) ∧
        ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ N : ℕ,
          RealTruncationBound m d x (overlapBox c₀ lo hi)
            (fun n => partitionCutoff m x d n ε) c C N := by sorry
