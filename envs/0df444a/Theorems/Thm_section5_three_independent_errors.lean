-- Prove2me | Theorems.Thm_section5_three_independent_errors
-- name    : section5_three_independent_errors
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:04.956266+00:00
-- url     : https://prove2.me/theorems/677c9566-b365-432b-82f7-fbd82652791c
-- title:
--   Majority error bound for three independent finite experiments
-- statement:
--   Let α,β,γ be finite spaces with nonnegative probability weights p,q,r each summing to one. Let P,Q,R be respective decidable error events, each with probability at most 1/4. Under their product distribution, $$\Pr[(P\cap Q)\cup(P\cap R)\cup(Q\cap R)]\le5/32.$$ Thus the probability that at least two errors occur is at most 5/32.
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5OrientationProbability.lean, lines 21–32.

import Mathlib
set_option autoImplicit false

theorem section5_three_independent_errors {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α → ℝ) (q : β → ℝ) (r : γ → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b) (hr : ∀ c, 0 ≤ r c)
    (hpt : ∑ a, p a = 1) (hqt : ∑ b, q b = 1) (hrt : ∑ c, r c = 1)
    (P : α → Prop) (Q : β → Prop) (R : γ → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hP : ∑ a ∈ Finset.univ.filter P, p a ≤ 1/4)
    (hQ : ∑ b ∈ Finset.univ.filter Q, q b ≤ 1/4)
    (hR : ∑ c ∈ Finset.univ.filter R, r c ≤ 1/4) :
    (∑ a : α, ∑ b : β, ∑ c : γ,
      if (P a ∧ Q b) ∨ (P a ∧ R c) ∨ (Q b ∧ R c) then p a*q b*r c else 0) ≤ 5/32 := by sorry
