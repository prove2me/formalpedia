-- Prove2me | Theorems.Thm_A166944Research_a166944_terminal_dichotomy
-- name    : A166944Research.a166944_terminal_dichotomy
-- status  : Proved
-- author  : @tara_sooo
-- created : 2026-11-19T06:02:43.553921+00:00
-- url     : https://prove2.me/theorems/ff4e63fb-838a-4cbc-8b6a-129ddfecbfd9
-- title:
--   An A166944 capped replay ends either quiet or by crossing the record
-- statement:
--   Let $a$ be the OEIS A166944 recurrence, $D_n=a_n-n$ its offset from the identity, and $B_n=a_n-2n+2$ the offset from the doubled index. A **moving-horizon state** $(s,C)$ is a pair with $D_s=C$ and $s<C$; a **step** from $(s,C)$ to $(r,C')$ is the first index $r>s$ where the increment $d_r$ exceeds $1$, followed by the resulting state $C'=D_r> C$.
--
--   Suppose $(s,C)$ is such a state, and $M$ is an attained running maximum of the differences up to $s$. Then the replay that follows from $(s,C)$ terminates in exactly one of two ways:
--
--   $$\bigl(B_{C_f}=2 \text{ and } d_j=1 \text{ for all } s_f<j\le C_f\bigr) \quad\text{or}\quad \bigl(\exists\, r,\ C',\ \text{a step } (s_f,C_f)\to(r,C') \text{ with } d_r>M\bigr).$$
--
--   Along the way the path never violates the cap: $M$ stays an attained maximum at the intermediate index $s_f$.
--
--   In words: a capped replay either **runs out quietly** -- no further nonunit increment appears before the horizon bound is reached, and the terminal state satisfies the fundamental identity $B_{C_f}=2$ -- or **crosses the record**, producing a difference strictly larger than $M$.
--
--   This is the case split on which the whole terminal argument rests. The quiet branch is where the twin-prime certificates are produced: the tail is unit, and a long enough tail forces $C_f\pm1$ to have no small divisor. The crossing branch is where the record grows, and it is certified by the growth bound on the offset rather than by any factor information.
--
--   **Why the dichotomy is not immediate.** Termination is not built into the definitions: a step can in principle be followed by arbitrarily many further steps, and the horizon bound is what forces the process to stop. The bound is the least common multiple of the positive odd integers up to $M$, which every increment is known to divide; once the offset exceeds it, no further old step is possible, so either a new record appears or the replay is finished.
-- source:
--   Derived within this development; the Mathlib-side original is RecordBarrier.capped_moving_horizon_eventual_exit. See https://github.com/tara-sooo/A166944-Lean

import Definitions.Def_a166944_moving_horizon
import Definitions.Def_a166944_B

open A166944Research

namespace A166944Research

theorem a166944_terminal_dichotomy {M s C : Nat}
    (hstate : IsMovingHorizonState s C) (hP : IsAttainedPreviousMaximum M s) :
    ∃ sf Cf p : Nat, HasMovingHorizonPathTo s C sf Cf p ∧
      IsAttainedPreviousMaximum M sf ∧
      ((B Cf = 2 ∧ ∀ j : Nat, sf < j → j ≤ Cf → d j = 1) ∨
        ∃ r C' : Nat, IsMovingHorizonStep sf Cf r C' ∧ M < d r) := by
  sorry

end A166944Research
