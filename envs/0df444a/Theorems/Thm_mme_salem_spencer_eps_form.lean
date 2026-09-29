-- Prove2me | Theorems.Thm_mme_salem_spencer_eps_form
-- name    : mme_salem_spencer_eps_form
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-31T17:51:54.392721+00:00
-- url     : https://prove2.me/theorems/919d5079-e872-4070-abe2-be96787ace83
-- statement:
--   **Salem–Spencer sets are asymptotically dense (the $\varepsilon$-form of Behrend's theorem).**
--
--   For every $\varepsilon>0$ there is a threshold $N_0$ such that for all $N\ge N_0$, the interval $\{0,1,\dots,N-1\}$ contains a finite set $S$ with no three-term arithmetic progression and
--
--   $$
--   |S|\;\ge\;N^{\,1-\varepsilon}.
--   $$
--
--   This is the standard $\varepsilon$-form of Behrend's 1946 density bound. It is the counting input of the laser method's hashing step: block indices of a tensor power are hashed into such a set $S$, and the near-linear density guarantees that only a subpolynomial fraction of blocks is lost, which is what makes the extracted direct sums large enough to drive the asymptotic sum inequality.
--
--   The statement is paper-agnostic and reusable by every laser-method argument (Strassen 1986–1988, Coppersmith–Winograd 1990, and the later improvements), which all consume exactly this form.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/AP/Three/Behrend.html

import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Real

theorem mme_salem_spencer_eps_form (ε : ℝ) (hε : 0 < ε) : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ ThreeAPFree (S : Set ℕ) ∧ (N : ℝ) ^ (1 - ε) ≤ (S.card : ℝ) := by sorry
