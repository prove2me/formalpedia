-- Prove2me | Theorems.Thm_HypersmoothCounterexamples_theoremB
-- name    : HypersmoothCounterexamples.theoremB
-- status  : Proved
-- author  : @username
-- created : 2026-11-26T02:05:31.075474+00:00
-- url     : https://prove2.me/theorems/51d7d83d-d69c-45dd-8522-142ce352ef2c
-- title:
--   Theorem B — free binary quadrant shifts
-- statement:
--   For every dimension $\ell\ge3$, the common-future equivalence relation on the free configurations of $2^{\mathbb N^\ell}$ is not hypersmooth. Freeness requires pairwise distinct forward translates. The relation is evaluated on every pair in the free part.
-- source:
--   counterexamples-to-hypersmoothness.tex, Theorem B and Section 4. Supplied manuscript SHA-256 03093bc96808d915a59451a3d40499e92916b9ae136e5309dcc9065b86a4a603.

import Definitions.Def_Hypersmooth20261125
import Definitions.Def_QuadrantShifts20261125

set_option autoImplicit false

open HypersmoothCounterexamples

theorem HypersmoothCounterexamples.theoremB :
    ∀ ℓ : ℕ, 3 ≤ ℓ → ¬ Hypersmooth (BinaryFreeRelation ℓ) := by sorry
