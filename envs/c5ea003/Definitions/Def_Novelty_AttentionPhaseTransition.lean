-- Prove2me | Definitions.Def_Novelty_AttentionPhaseTransition
-- name    : Novelty_AttentionPhaseTransition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:06:29.156412+00:00
-- url     : https://prove2.me/theorems/69a886f6-2bad-48c2-9821-08cb3f0e6488
-- title:
--   Aether Catalog definitions — Novelty_AttentionPhaseTransition
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AttentionPhaseTransition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AttentionPhaseTransition.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_AttentionRetentionKnee
import Definitions.Def_Novelty_AttentionScaleThreshold

/-!
# The increment accelerates at 4096: a phase transition in the attention budget (NET-78)

NET-78 extends the 0.5B knee chain of NET-67 by one context octave.  Writing
`j` for the number of context doublings above the base context `512`
(so `j = 0,1,2,3` is `ctx = 512, 1024, 2048, 4096`), the measured knees are

| j        | 0  | 1  | 2  | 3  |
|----------|----|----|----|----|
| `k*`     | 16 | 20 | 24 | 40 |

with increments `+4, +4, +16`.  The verdict extracted from the run is
**THE-INCREMENT-ACCELERATES-AT-4096**: the affine law `16 + 4j` of cycle 1
(`Novelty.AttentionBudgetIncrement`) breaks at the fourth doubling.

This file is the formal audit of that verdict.  It has four layers.

**1. Discrete layer.**  `kneeSmall_refuted` and `no_affine_fits` prove the two
refutations exactly (`P1`: the `+4` law does not continue; `P2`: no saturation).
But the four data points are far from determining the continuation:
`kneeRamp`, `kneeCubic` and `kneeQuad` all reproduce `16, 20, 24, 40` and
predict `56`, `80`, `92` at `ctx = 8192` (`fits_underdetermined`).  What *is*
forced, under the (measured) discrete convexity of the chain, is a sharp lower
bound: `convex_growth` gives `f (m+3) ≥ 40 + 16m`, hence at least `56` keys at
`8192` and no finite universally safe budget (`no_uniform_budget`).

**2. Tropical layer.**  The minimal convex fit is a two-term max-plus
polynomial, `kneeRamp j = max (16 + 4j) (16j - 8)` (`kneeRamp_eq_max`), and its
tropical corner — the unique crossing of the two affine pieces — sits at
`j = 2`, i.e. at `ctx = 2048` (`transition_at_2048`).  So "budgets are stable
for the first ~2000 tokens, then sharply more expensive" is not a narrative
gloss: it is the location of the tropical root of the fitted budget law.

**3. Gate layer (barrier (c), confronted).**  The knee was read on the coarse
grid `{16,20,24,28,32,40}`, so the reported `40` is a grid point, not a
measurement.  `gate_bracket` recovers the gate `τ` from the table
(`0.979 < τ ≤ 0.984`), `true_knee_bracket` shows every profile consistent with
the table has its true knee in `[33, 40]`, and `bracket_sharp` exhibits two
explicit profiles realising both endpoints.  Consequently
`acceleration_bracketed`: the data force an increment in `[9, 16]`, i.e. an
acceleration factor in `[9/4, 4]`.  **The direction of the verdict is proved;
the advertised factor `4` is the top of a bracket whose bottom is `2.25`.**

**4. Continuous layer.**  Cycle 1 derived the `+4` law from a decay rate
degrading as `λ_j = λ₀/(j+1)`.  `lamAt_law_refuted` shows that family is now
strictly refuted: it is affine in `j`, and the chain is not.
`rate_collapse_accelerates` replaces it with a *model-free* consequence: for any
exponential-tail explanation of the chain, `λ_j = log(1/δ)/k_j`, so
`λ₃/λ₂ < λ₂/λ₁` — and `rate_collapse_accelerates_robust` proves this
**for every knee value in the grid bracket `[33,40]`**.  The phase transition
therefore survives the grid gap even though the factor `4` does not.  Finally
`calibration_phase` calibrates the crossover rate family `lamCross` against the
whole measured chain at the cycle-1 tail budget `δ = e⁻⁴`.

**Deployment.**  `cache24_fails_robust` proves the deployment corollary in its
grid-robust form: a 24-key cache fails at `ctx = 4096` for *every* profile
consistent with the table, and `provably_unsafe` / `certified_safe` delimit
exactly which budgets the measurement decides.
-/

namespace Catalog.Novelty.AttentionPhaseTransition

open Catalog.Novelty.AttentionBudgetIncrement Catalog.Novelty.AttentionRetentionKnee

/-! ### 1. The measured chain and the death of the affine law -/

/-- A budget law *fits the NET-78 chain* if it reproduces the four measured
knees `16, 20, 24, 40` at context doublings `j = 0,1,2,3`. -/
def Fits (f : ℕ → ℕ) : Prop := f 0 = 16 ∧ f 1 = 20 ∧ f 2 = 24 ∧ f 3 = 40




/-! ### 2. Three continuations, all fitting the same four points -/

/-- **Ramp fit**: linear with a kink at `j = 2` (increment `+4` then `+16`). -/
def kneeRamp (j : ℕ) : ℕ := 16 + 4 * j + 12 * (j - 2)

/-- **Cubic fit**: the Newton interpolation polynomial through the four points,
`16 + 4·C(j,1) + 0·C(j,2) + 12·C(j,3)`. -/
def kneeCubic (j : ℕ) : ℕ := 16 + 4 * j + 12 * j.choose 3

/-- **Quartic-rate fit**: the increment itself multiplies by `4` at every
doubling past the transition. -/
def kneeQuad (j : ℕ) : ℕ := 16 + 4 * j + 4 * (4 ^ (j - 2) - 1)






/-! ### 3. What convexity does force -/

/-- Discrete convexity: the per-doubling increments never decrease.  This is the
shape actually observed (`+4, +4, +16`) and the shape of every hinge law in
`Novelty.AttentionScaleThreshold`. -/
def ConvexLaw (f : ℕ → ℕ) : Prop := ∀ j, 2 * f (j + 1) ≤ f j + f (j + 2)








/-! ### 4. Tropical layer: the transition is a max-plus corner at ctx = 2048 -/




/-! ### 5. Gate layer: the coarse grid and what it really proves -/

/-- The measured retention table at `ctx = 4096` (6 held-out windows, exact
gate), as a predicate on a profile: retention at the six grid points. -/
def MatchesTable (p : ℕ → ℝ) : Prop :=
  retained p 16 = 959 / 1000 ∧ retained p 20 = 969 / 1000 ∧
  retained p 24 = 975 / 1000 ∧ retained p 28 = 977 / 1000 ∧
  retained p 32 = 979 / 1000 ∧ retained p 40 = 984 / 1000




/-- An explicit profile reproducing the whole measured table whose true knee is
`33`: all its post-`32` mass arrives at index `32`. -/
noncomputable def pLow : ℕ → ℝ := fun i =>
  if i = 0 then 959 / 1000 else if i = 16 then 10 / 1000 else if i = 20 then 6 / 1000
  else if i = 24 then 2 / 1000 else if i = 28 then 2 / 1000 else if i = 32 then 5 / 1000
  else 0

/-- An explicit profile reproducing the whole measured table whose true knee is
`40`: the same mass arrives at index `39`. -/
noncomputable def pHigh : ℕ → ℝ := fun i =>
  if i = 0 then 959 / 1000 else if i = 16 then 10 / 1000 else if i = 20 then 6 / 1000
  else if i = 24 then 2 / 1000 else if i = 28 then 2 / 1000 else if i = 39 then 5 / 1000
  else 0








/-! ### 6. Deployment: which budgets the measurement decides -/





/-! ### 7. Continuous layer: the rate law of cycle 1 is refuted -/





/-! ### 8. A crossover rate family that fits the whole chain -/

/-- Decay rate after `j` doublings in the **crossover** family: the inverse rate
grows like `4 + j` before the transition and picks up an extra `3` per doubling
after it. -/
noncomputable def lamCross (lam0 : ℝ) (j : ℕ) : ℝ :=
  lam0 / (4 + (j : ℝ) + 3 * max ((j : ℝ) - 2) 0)







end Catalog.Novelty.AttentionPhaseTransition


