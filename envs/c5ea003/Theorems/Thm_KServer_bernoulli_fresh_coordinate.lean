-- Prove2me | Theorems.Thm_KServer_bernoulli_fresh_coordinate
-- name    : KServer.bernoulli_fresh_coordinate
-- status  : Proved
-- author  : @kwal0203
-- created : 2026-10-30T17:32:54.710958+00:00
-- url     : https://prove2.me/theorems/65388832-645a-4cdc-b46c-5bd3b6f8f6c1
-- title:
--   An unused Bernoulli seed retains its bias on every history event
-- statement:
--   Let $I$ be a finite index set and choose biases $p_i\in[0,1]$. For each Boolean vector $x\in\{0,1\}^I$, define
--
--   $$P(x)=\prod_{i\in I}w_i(x_i),\qquad w_i(1)=p_i,\quad w_i(0)=1-p_i.$$
--
--   These weights are nonnegative and normalized:
--
--   $$P(x)\ge0,\qquad \sum_xP(x)=1.$$
--
--   Fix a coordinate $i$ and an event $A$ closed under flipping that coordinate. Then
--
--   $$\sum_{x\in A,\,x_i=1}P(x)=p_i\sum_{x\in A}P(x).$$
--
--   This is the finite independence statement needed when an algorithm chooses a seed coordinate that its current history has not revealed. The event may have zero mass, and biases may be zero or one; the identity does not divide by any probability.
--
--   **Formalization Note** The event hypothesis is stated as one-way closure under the coordinate flip. Since that flip is an involution, this is equivalent to invariance. The empty index set is allowed.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1, stage 2a (independent sampling and the left/right probabilities), and Section 4.2, equations (3)–(4), printed pp. 16–19. Elementary finite-product probability lemma formalized here; normalization uses Mathlib Fintype.prod_sum. This is not quoted as a separate theorem in the paper.

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

theorem KServer.bernoulli_fresh_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (P : (ι → Bool) → ℝ) (hP : ∀ x, P x = ∏ i, if x i then p i else 1 - p i) :
    (∀ x, 0 ≤ P x) ∧ (∑ x, P x) = 1 ∧
    ∀ (i : ι) (A : (ι → Bool) → Prop) [DecidablePred A],
      (∀ x, A x → A (Function.update x i (!(x i)))) →
      (∑ x ∈ Finset.univ.filter (fun x => A x ∧ x i = true), P x) =
        p i * ∑ x ∈ Finset.univ.filter A, P x := by sorry
