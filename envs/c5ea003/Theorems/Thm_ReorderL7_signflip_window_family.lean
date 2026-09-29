-- Prove2me | Theorems.Thm_ReorderL7_signflip_window_family
-- name    : ReorderL7.signflip_window_family
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:28:07.710305+00:00
-- url     : https://prove2.me/theorems/04b17d3c-15de-4a3b-8fa4-0b58b2720cb1
-- title:
--   Sign-flip law for a general window ratio.
-- statement:
--   **Sign-flip law for a general window ratio.**  On the uniform band
--   `r ~ U[1,1+δ]`, the window-ascending policy of a generator advertising `q < k·p`
--   beats the window-descending one **iff** `δ > 8√k(√k-1)/(√k+1)²`.
--
--   ```lean
--   theorem ReorderL7.signflip_window_family{k delta : ℝ} (hk : 1 < k) (h : 0 < delta) :
--       (meanInvSqrt delta - 1 / Real.sqrt k < 1 - meanInvSqrt delta) ↔ crossoverWidthK k < delta := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ReorderWindowFamilyKeepFraction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ReorderWindowFamilyKeepFraction.lean#L72

-- Thm stub generated from Novelty/ReorderWindowFamilyKeepFraction.lean
import Mathlib
import Definitions.Def_Novelty_ReorderExtremalitySignFlip
import Definitions.Def_Novelty_ReorderFrontLoadingCertification
import Definitions.Def_Novelty_ReorderWindowFamilyKeepFraction
/-
# The sign flip is universal across window families, and the wheel law is a theorem

Fourth instalment of the GAP-L7' programme.  Two closures:

## A.  Window-ratio family : the sign flip is not an artefact of `q < 2p`

A generator that advertises `q < k·p` licenses the balance window
`[√N/√k, √N]`.  Repeating the round-76 analysis for a general window ratio gives
a closed-form crossover

`δ*(k) = 8√k(√k - 1)/(√k + 1)²`

(`signflip_window_family`), specialising to `80 - 56√2` at `k = 2`
(`crossoverWidthK_two`).  The decisive structural fact is

`crossoverWidthK_lt_band : 1 < k → δ*(k) < k - 1`,

i.e. **the crossover always lies strictly inside the admissible band range**.
So for *every* advertised balance ratio there are two admissible populations on
which the same two committed policies swap winners
(`signflip_universal`): the falsification of GAP-L7-as-drafted is not a corner
of the `q < 2p` convention, it is a property of the whole REORDER family.

## B.  L7-d : the structural keep fraction, extracted rather than booked

`card_coprime_block` counts the survivors of a mod-`M` wheel exactly:
`φ(M)·m` out of `M·m`.  Since a reordering is a bijection it cannot change that
count (`touched_card_reorder_invariant`), so `μ_eff = φ(M)/M` is a *conserved
quantity of the transcript*, not an experimenter's booking.  Feeding it into the
touch floor gives the protocol-A T1 law as a theorem:

`wheel_speedup_le : S ≤ M/φ(M)`,  and at `M = 30`,  `S ≤ 15/4 = 3.75`
(`wheel_thirty_law`) — the value the wheel arm measured as 3.7331–3.7496.

-- !-- Lab Notes -- !--
-- Monte-Carlo (n = 1500 per band, seed 20260831, genuine 24-bit semiprimes)
-- brackets the k = 2 crossover between delta = 0.80 (ascending still wins,
-- desc/asc = 1.0200) and delta = 0.75 (descending wins, desc/asc = 0.9273),
-- against the closed form 80 - 56*sqrt 2 = 0.804041 proved here.
-- Measured wheel speedups 3.7331 / 3.741 / 3.7496 sit under the derived
-- 15/4 = 3.75 ceiling, gaps 0.45% / 0.24% / 0.01%.
-/

open ReorderL7

open Finset

noncomputable section

/-! ## A.  The window-ratio family -/

theorem ReorderL7.signflip_window_family{k delta : ℝ} (hk : 1 < k) (h : 0 < delta) :
    (meanInvSqrt delta - 1 / Real.sqrt k < 1 - meanInvSqrt delta) ↔ crossoverWidthK k < delta := by sorry
