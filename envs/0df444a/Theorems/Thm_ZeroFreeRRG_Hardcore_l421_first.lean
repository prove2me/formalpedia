-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_l421_first
-- name    : ZeroFreeRRG.Hardcore.l421_first
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:12:19.021915+00:00
-- url     : https://prove2.me/theorems/0a62e187-7f82-4c9f-a654-a0be9e71cde3
-- title:
--   Lemma 4.21, Step 4: uniform first-moment lower and upper bounds
-- statement:
--   Let $t$ be a nontrivial parameter satisfying Condition 2, and let $x$ be a positive nontrivial parameter used as the real comparison point. There are a disk $D$ about $t$, $a_0>0$, $A_0$, and $N$ such that, for every admissible $n\ge N$,
--   $$a_0\le |a_n(z)|\quad(z\in D),\qquad a_n(x)\le A_0.$$
--
--   The lower bound follows from Lemma 5.5(1): $a_n$ converges locally uniformly to a holomorphic function that is nowhere zero on a sufficiently small disk. The upper bound at $x$ is the uniform first-moment control used in Step 4 of Appendix E.4. For the two explicit kernels, the hypothesis $\kappa_a(t)\le0$ required by Lemma 5.5 is automatic at a nontrivial real parameter.
--
--   **Formalization Note.** This uses the same statement as `lemma_4_21_first_moment_bounds`, with a short identifier for the import resolver.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), Appendix E.4, Step 4, p. 83 (printed), using Lemma 5.5(1), p. 39 (printed), and the eigenvalue formulas (6)–(7), p. 16 (printed).

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Definitions.Def_ZeroFreeRRG_Hardcore_Truncation

open scoped Classical

open AFIsingKS
open ZeroFreeRRG.Hardcore

/-- **First-moment bounds for Lemma 4.21** (Appendix E.4, Step 4, using Lemma 5.5(1)). Near a
nontrivial parameter satisfying Condition 2, `a_n` is bounded below in modulus uniformly on a
disk; at the positive comparison parameter its real first moment is bounded above. -/
theorem ZeroFreeRRG.Hardcore.l421_first
    (m : Model) (hm : m.Valid) (d : ℕ) (hd : 3 ≤ d)
    (t : ℝ) (ht : m.Nontrivial t) (hC2 : Condition2 m d t) (x : ℝ) (hx : m.PosParam x) :
    FirstMomentBounds m d t x := by sorry
