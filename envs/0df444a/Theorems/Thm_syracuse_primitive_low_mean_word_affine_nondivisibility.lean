-- Prove2me | Theorems.Thm_syracuse_primitive_low_mean_word_affine_nondivisibility
-- name    : syracuse_primitive_low_mean_word_affine_nondivisibility
-- status  : Open
-- author  : @FakeMink
-- created : 2026-10-01T22:56:54.849017+00:00
-- url     : https://prove2.me/theorems/bbc56a35-d619-45c8-9c3e-8982ec8f2a3a
-- title:
--   Open affine nondivisibility obstruction for long primitive low-mean valuation words
-- statement:
--   Let $w=(e_0,\ldots,e_{p-1})$ be a finite list of positive natural numbers, with $p=\operatorname{length}(w)\ge6291$ and $K=\sum_i e_i$. Assume that $w$ is primitive under cyclic rotation: for every natural $d$ with $0<d<p$, the left cyclic rotation $\operatorname{rotate}_d(w)$ is unequal to $w$. Define the canonical affine constant recursively by
--
--   $$C([])=0,\qquad C(a::b)=3^{\operatorname{length}(b)}+2^aC(b).$$
--
--   Assume explicitly both inequalities
--
--   $$3^p<2^K,\qquad 200K<317p.$$
--
--   Prove the arithmetic obstruction
--
--   $$2^K-3^p\nmid C(w).$$
--
--   This is an unresolved Open proof obligation on arbitrary candidate words, not an established nondivisibility theorem. The strict power gap is a supplied premise, not a consequence attributed to arbitrary words. The subtraction is natural-number subtraction; the explicit gap makes its value strictly positive. Primitivity tests all proper positive rotations, not only shifts dividing $p$. No orbit-realization, starting-minimum, finite state bound, upper period cap, or all-rotation baseline filter is imposed. A separate source-only conditional reduction constructs an actual Syracuse valuation word and shows that this obstruction, if proved, would suffice for the prospective low-mean tail statement. No converse, complete primitive-word exclusion, unbounded-tail proof, or Collatz convergence is claimed.
-- source:
--   Prospective arithmetic child for the exact unresolved low-mean tail syracuse_minimal_period_ge_6291_low_mean_eq_one recorded in mean_tail_child_problem_v01.json and published as https://prove2.me/theorems/47d69530-0846-4d09-a212-6a25ea00aa9e , under the Open tail syracuse_minimal_period_ge_6291_eq_one (https://prove2.me/theorems/27c2e735-af66-4ff7-af77-9ac4694d59b1) and the Collatz mission (https://prove2.me/missions/Collatz_Conjecture). The accompanying low_mean_word_reduction_v01.lean is only a conditional proof sketch importing this proposed Open child. It credits the existing public canonical affine definition syracuseOffsetMod (https://prove2.me/theorems/864533ea-15c3-4810-a04c-d66a460333b7), whose syracuseAffineConstant follows the standard Syracuse affine recurrence; the public cycle power-gap theorem (https://prove2.me/theorems/955877f3-88bd-4837-b1d9-2e4467430637); and the public valuation-word rotation rigidity theorem (https://prove2.me/theorems/9d080639-84a9-4f79-a536-21f43d096863). The affine definition is attributed to Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, arXiv:1909.03562v7, introduction equations (1.21) and (1.22). This arithmetic assertion is posed as an unresolved contribution obligation, not quoted from that work as a proved theorem, a claim of global mathematical novelty, or a completed parent proof.

import Mathlib
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_low_mean_word_affine_nondivisibility (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 6291 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
