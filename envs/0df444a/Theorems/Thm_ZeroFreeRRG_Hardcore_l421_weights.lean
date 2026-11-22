-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_l421_weights
-- name    : ZeroFreeRRG.Hardcore.l421_weights
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:10:20.655384+00:00
-- url     : https://prove2.me/theorems/389f921b-8c34-45ed-9da0-381676bbfc44
-- title:
--   Lemma 4.21, Step 4: complex-versus-positive weight comparison at a positive parameter
-- statement:
--   Fix a positive nontrivial parameter $x$ and an overlap box $B$. For every $k>0$, after shrinking the complex disk about $x$ sufficiently, there is $A>0$ such that, uniformly for configurations and $z,w$ in that disk,
--   $$
--   \begin{aligned}
--   |\mathcal Z_G(z)|&\le A e^{kn}\mathcal Z_G(x),\\
--   |\mathcal Z^{(2)}_{G,B}(z,w)|&\le A e^{kn}\mathcal Z^{(2)}_{G,B}(x,x),\\
--   |\mathcal Z_G(z)\mathcal Z_G(w)-\mathcal Z^{(2)}_{G,B}(z,w)|
--   &\le A e^{kn}\bigl(\mathcal Z_G(x)^2-\mathcal Z^{(2)}_{G,B}(x,x)\bigr).
--   \end{aligned}
--   $$
--
--   This is the positive-parameter comparison in Step 4 of Appendix E.4. Termwise continuity of $\pi(z)$ and $M(z)$ at $x>0$ controls each configuration weight by its positive weight times $\exp\{O(n(|z-x|+|w-x|))\}$.
--
--   **Formalization Note.** This uses the same statement as `lemma_4_21_positive_weight_comparison`, with a short identifier for the import resolver.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), Appendix E.4, Step 4, p. 83 (printed), positive-parameter weight comparison.

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Truncation

open scoped Classical

open AFIsingKS
open ZeroFreeRRG.Hardcore

/-- **Lemma 4.21, positive weight comparison** (Appendix E.4, Step 4). At a positive parameter,
for every prescribed exponential rate `k > 0` there is a disk on which the three restricted
configuration sums are bounded by their positive real values with loss at most `A exp(kn)`. -/
theorem ZeroFreeRRG.Hardcore.l421_weights
    (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d)
    (x : ℝ) (hx : m.PosParam x) (B : Set (m.Spin × m.Spin → ℝ)) (k : ℝ) (hk : 0 < k) :
    ∃ A R : ℝ, WeightComparison m d x x B A k R := by sorry
