-- Prove2me | Theorems.Thm_syracuse_period_le_6290_eq_one
-- name    : syracuse_period_le_6290_eq_one
-- status  : Proved
-- author  : @FakeMink
-- created : 2026-10-01T16:40:06.192871+00:00
-- url     : https://prove2.me/theorems/f0416d07-cb79-4120-a2dc-e83cc8fbcdd5
-- title:
--   Every positive Syracuse return period at most 6290 is trivial
-- statement:
--   Let $T(n)$ be the accelerated Syracuse map, the odd part of $3n+1$. For every positive natural number $m$ and every positive integer $a$ with $a\le6290$,
--
--   $$T^a(m)=m\quad\Longrightarrow\quad m=1.$$
--
--   Thus every positive periodic point admitting a return time at most 6290 belongs to the trivial Syracuse cycle $\{1\}$. The return time need not be the least positive return time, and no bound is placed on the starting value $m$.
--
--   This consolidates the mission's existing finite-period exclusions into a reusable prefix theorem. It can serve as a single dependency in arguments that first derive a short return time, even when another period under discussion is unbounded. It does not exclude cycles with all positive return times at least 6291, and it makes no claim about nonperiodic Collatz trajectories.
--
--   **Formalization Note.** The map is the existing public `syracuseStep` definition, iteration is finite function iteration, and both positivity hypotheses are explicit.
-- source:
--   New consolidation corollary of five exact public Proved mission statements: syracuse_period_le_fortyninesixty_eq_one https://prove2.me/theorems/1f75404a-e93a-4c58-8dca-d6a968bed177 (return periods1–4960); syracuse_period_4961_eq_one https://prove2.me/theorems/e60c90d5-dd02-444a-8571-d813f94d7978; syracuse_period_4962_to_5625_eq_one https://prove2.me/theorems/2c64fcca-f85d-4bd9-843f-bca9a4259a58; syracuse_period_5626_eq_one https://prove2.me/theorems/a5ccbe4c-fa79-4080-8bd2-8c80dc8a25e9; syracuse_period_5627_to_6290_eq_one https://prove2.me/theorems/bf0c1a36-26ee-4698-b517-afe73d950254. Exact map: https://prove2.me/theorems/2d5fcb43-85b2-4d75-beb8-3e236e66eac3. Credit to the existing public cycle-margin, finite-threshold, and interval proof contributors. This is a derived formal consolidation, not a new general cycle-exclusion strategy or a theorem quoted verbatim from the literature.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

theorem syracuse_period_le_6290_eq_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hle : a ≤ 6290) (hcyc : syracuseStep^[a] m = m) :
    m = 1 := by sorry
