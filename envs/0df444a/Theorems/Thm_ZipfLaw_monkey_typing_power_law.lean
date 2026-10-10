-- Prove2me | Theorems.Thm_ZipfLaw_monkey_typing_power_law
-- name    : ZipfLaw.monkey_typing_power_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:34:22.855851+00:00
-- url     : https://prove2.me/theorems/fee6ee30-fa71-411e-a302-0bdf2fbf1bd7
-- title:
--   Random typing produces a power law in rank (Li's model)
-- statement:
--   Consider a monkey typing on a keyboard with $m\ge2$ letter keys, each pressed with the same probability $q>0$, and a space bar pressed with probability $1-mq>0$. The probability that the word following a space is exactly the string $w$ of letters is $p(w)=q^{|w|}(1-mq)$. List all nonempty words in order of non-increasing probability, $w_1,w_2,w_3,\dots$ (ties in any order). Then the probability of the word of rank $r$ obeys a power law in $r$: with $\alpha=\log_m(1/q)$ there are constants $0<C_1\le C_2$ such that for all $r\ge1$
--   $$C_1\,r^{-\alpha}\le p(w_r)\le C_2\,r^{-\alpha}.$$
--
--   **Formalization Note.** Ranks are $0$-indexed in Lean: the rank order is a bijection $e:\mathbb N\to\{\text{nonempty words}\}$ along which $p$ is non-increasing, and the bound is stated with $(r+1)^{-\alpha}$.
-- source:
--   Wikipedia, "Zipf's law" (https://en.wikipedia.org/wiki/Zipf%27s_law), snapshot uploaded by the proposer, section "Statistical explanations" (Li: "in a document in which each character has been chosen randomly from a uniform distribution of all letters (plus a space character), the 'words' with different lengths follow the macro-trend of Zipf's law"; ref. Li 1992, https://doi.org/10.1109/18.165464).

import Mathlib
import Definitions.Def_ZipfLaw_Defs

namespace ZipfLaw

theorem monkey_typing_power_law (m : ℕ) (hm : 2 ≤ m) (q : ℝ) (hq : 0 < q) (hmq : (m : ℝ) * q < 1)
    (e : ℕ → List (Fin m)) (he_inj : Function.Injective e)
    (he_range : Set.range e = {w | w ≠ []})
    (he_sorted : Antitone (fun r => monkeyWordProb m q (e r))) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ r : ℕ,
      C₁ * ((r : ℝ) + 1) ^ (-Real.logb m (1 / q)) ≤ monkeyWordProb m q (e r) ∧
        monkeyWordProb m q (e r) ≤ C₂ * ((r : ℝ) + 1) ^ (-Real.logb m (1 / q)) := by sorry

end ZipfLaw
