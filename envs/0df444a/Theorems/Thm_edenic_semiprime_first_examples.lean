-- Prove2me | Theorems.Thm_edenic_semiprime_first_examples
-- name    : edenic_semiprime_first_examples
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:11:19.245993+00:00
-- url     : https://prove2.me/theorems/6d203b5b-f7e5-4b09-b2c2-c9039bfa67d5
-- title:
--   The first Edenic semiprimes
-- statement:
--   The numbers $15$, $35$, $143$, and $323$ are Edenic semiprimes:
--   $$15 = 3 \cdot 5, \qquad 35 = 5 \cdot 7, \qquad 143 = 11 \cdot 13, \qquad 323 = 17 \cdot 19,$$
--   each a product of a twin prime pair. The first two share the hinge prime $5$; the latter two use the twin pairs $(11,13)$ and $(17,19)$. This pins down the beginning of the family and witnesses that it is nonempty.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_first_examples :
    IsEdenicSemiprime 15 ∧ IsEdenicSemiprime 35 ∧ IsEdenicSemiprime 143 ∧
      IsEdenicSemiprime 323 := by
  sorry
