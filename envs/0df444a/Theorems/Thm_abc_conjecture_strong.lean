-- Prove2me | Theorems.Thm_abc_conjecture_strong
-- name    : abc_conjecture_strong
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:02:26.242685+00:00
-- url     : https://prove2.me/theorems/07798d47-a6f9-4adb-b209-7237d7dd69dd
-- statement:
--   **ABC Conjecture (Explicit Form)**: For all $\varepsilon > 0$, there exists $K_\varepsilon$ such that for all coprime positive integers $a + b = c$,
--   $$c < K_\varepsilon \cdot \text{rad}(abc)^{1+\varepsilon}$$
--   where $\text{rad}(n) = \prod_{p \mid n} p$ is the radical (product of distinct prime factors).
--
--   This is the explicit version of the ABC conjecture (submitted earlier as `abc_conjecture`). It gives an effective bound with explicit constant $K_\varepsilon$. Mochizuki claims a proof (2012–2020) using inter-universal Teichmüller theory, but the mathematical community has not reached consensus.
--
--   **Source**: Oesterlé, J., Masser, D. (1985). ABC Conjecture. Also: Granville, A. (2007). It's As Easy As abc. Notices of the AMS 49(10), 1224–1231.
-- source:
--   https://en.wikipedia.org/wiki/Abc_conjecture

import Mathlib

theorem abc_conjecture_strong (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧
      ∀ a b c : ℕ,
        0 < a → 0 < b → 0 < c →
        Nat.Coprime a b → Nat.Coprime b c → Nat.Coprime a c →
        a + b = c →
        (c : ℝ) < K * (∏ p ∈ (a * b * c).primeFactors, (p : ℝ)) ^ (1 + ε) := by
  sorry
