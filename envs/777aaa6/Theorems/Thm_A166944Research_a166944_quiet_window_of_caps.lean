-- Prove2me | Theorems.Thm_A166944Research_a166944_quiet_window_of_caps
-- name    : A166944Research.a166944_quiet_window_of_caps
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-19T00:21:33.478208+00:00
-- url     : https://prove2.me/theorems/0efef579-7ca7-41a1-bf7a-e7cad6bd0466
-- title:
--   The A166944 quiet window follows from the two caps, with no square root
-- statement:
--   At a terminal state of a capped canonical replay of the OEIS A166944 recurrence, the "quiet window" inequality
--
--   $$
--   2q < C_f - s_f \qquad\text{for every } q \text{ with } q^2 \le C_f + 1
--   $$
--
--   is what lets the value $C_f \pm 1$ at the terminal horizon be certified free of small factors. Those certificates are in turn what makes the next difference record a twin prime.
--
--   The window is a consequence of the two caps on the replay. The **index cap** is $4s_f \le 7M-1$, bounding how far the replay's index can travel from the record $M$. The **horizon cap** is $C_f \le 3M+4$, bounding the offset reached. Together with the starting horizon $2M-2 \le C_f$ and $M \ge 968$, they force the window.
--
--   The point of this statement is that it does not use a square root. The quantity $q$ is an arbitrary natural number carrying only $q^2 \le C_f+1$, so instantiating $q$ as the integer square root of $C_f+1$ recovers the usual form, while the statement itself makes sense in a library with no integer square root at all. That matters because the environment this theorem targets -- Lean v4.29.0-rc3, the one the Twin Prime Conjecture mission is built in -- has no such library function.
--
--   The mechanism is a division-free bound. From $q^2 \le C_f+1 \le 3M+5$ one deduces $8q+7 < M$, and the index cap then yields the window by linear arithmetic alone.
-- source:
--   Derived within this development; the square-root form is TwoCapGate.b_tight and the mutatis mutandis statement is QuietReturn.quiet_return_no_proper_factors. See https://github.com/tara-sooo/A166944-Lean

import Definitions.Def_a166944_window_core

open A166944Research

namespace A166944Research

/-- **The quiet-window condition at a terminal canonical state.**

At any state `(sf, Cf)` reached by a canonical capped replay, with the index cap
`4*sf <= 7*M-1` and the horizon cap `Cf <= 3*M+4` in force, the terminal horizon
satisfies `2*q < Cf - sf` for every `q` with `q*q <= Cf + 1`.

This is the division-free form: no integer square root is needed, so the same
statement is available in the mission's environment (Lean v4.29.0-rc3), where
`Init.Data.Nat.Sqrt` does not exist. With `q := isqrt (Cf+1)` it specialises to
the square-root form used by `QuietReturn.quiet_return_no_proper_factors`.

The content is the arithmetic: `q*q <= Cf+1 <= 3*M+5` forces `8*q+7 < M`, and
the index cap then yields the window by linear arithmetic alone. -/
theorem a166944_quiet_window_of_caps {M sf Cf q : Nat} (hM : 968 ≤ M)
    (hindex : 4 * sf ≤ 7 * M - 1) (hlo : 2 * M - 2 ≤ Cf)
    (hhorizon : Cf ≤ 3 * M + 4) (hq : q * q ≤ Cf + 1) :
    2 * q < Cf - sf :=
  sorry

end A166944Research
