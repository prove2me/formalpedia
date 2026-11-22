-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_lemma_4_21_step4_generic
-- name    : ZeroFreeRRG.Hardcore.lemma_4_21_step4_generic
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:05:13.461174+00:00
-- url     : https://prove2.me/theorems/99bae562-8f38-4f2e-9df2-58d83c1e7dc0
-- title:
--   Lemma 4.21, Step 4: analytic continuation of the real cutoff estimates
-- statement:
--   Let $E_n$ be graph cutoffs for which the real error sums at $x$ are $O(e^{-cn}a_n(x))$ and $O(e^{-cn}a_n(x)^2)$. Suppose that on a disk about $t$ all three complex configuration sums compare with their real values at $x$ with loss $Ae^{kn}$, and that $a_n$ has the usual uniform lower bound near $t$ and upper bound at $x$. If $c-2k>0$, then there are a smaller disk about $t$, $\gamma>0$, $C'$, and $N'$ for which
--   $$
--   \begin{aligned}
--   \bigl|\mathbb E[(\mathcal Z_G(t)^2-\mathcal Z^{(2)}_{G,B}(t,t))\mathbf 1\{E_n\}]\bigr|
--   &\le C'e^{-\gamma n}|a_n(t)|^2,\\
--   |\mathbb E[\mathcal Z_G(z)\mathbf 1\{E_n\}]-a_n(z)|
--   &\le C'e^{-\gamma n}|a_n(z)|,\\
--   |\mathbb E[\mathcal Z_G(z)\mathcal Z_G(w)\mathbf 1\{E_n\}]
--   -\mathbb E[\mathcal Z^{(2)}_{G,B}(z,w)]|
--   &\le C'e^{-\gamma n}|a_n(z)a_n(w)|,
--   \end{aligned}
--   $$
--   uniformly on that disk.
--
--   The proof is the finite-average argument in Step 4 of Appendix E.4: subtract the untruncated sum, apply the configurationwise comparisons, use the real error bounds, and divide by the uniform first-moment lower bounds. Any $\gamma<c-2k$ works after enlarging $C'$; one may take $\gamma=c-2k$ in the normalization used here.
--
--   **Formalization Note.** `ComplexTruncationBound` is exactly the target shape of Lemma 4.21. The theorem chooses the smaller of the weight-comparison and first-moment disks.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), Appendix E.4, Step 4, p. 83 (printed), derivation of (31) from (76).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Truncation

open scoped Classical

open AFIsingKS
open ZeroFreeRRG.Hardcore

/-- **Generic analytic-continuation step of Lemma 4.21** (Appendix E.4, Step 4). Real cutoff
errors with rate `c`, configurationwise complex weight comparison with rate `k`, and uniform
first-moment bounds imply the complex truncation estimate with rate `c - 2k`. -/
theorem ZeroFreeRRG.Hardcore.lemma_4_21_step4_generic
    (m : Model) (d : ℕ) (t x : ℝ)
    (B : Set (m.Spin × m.Spin → ℝ)) (E : ∀ n : ℕ, Set (Matching n d))
    (c C : ℝ) (N : ℕ) (A k R : ℝ)
    (hReal : RealTruncationBound m d x B E c C N)
    (hCompare : WeightComparison m d t x B A k R)
    (hFirst : FirstMomentBounds m d t x) (hγ : 0 < c - 2 * k) :
    ∃ R' : ℝ, 0 < R' ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ C' : ℝ, ∃ N' : ℕ,
      ComplexTruncationBound m d t B E R' γ C' N' := by sorry
