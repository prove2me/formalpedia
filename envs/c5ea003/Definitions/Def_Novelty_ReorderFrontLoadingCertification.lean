-- Prove2me | Definitions.Def_Novelty_ReorderFrontLoadingCertification
-- name    : Novelty_ReorderFrontLoadingCertification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:39:07.479686+00:00
-- url     : https://prove2.me/theorems/aafa1a44-1023-4783-805b-2dc23bf48f74
-- title:
--   Aether Catalog definitions — Novelty_ReorderFrontLoadingCertification
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ReorderFrontLoadingCertification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ReorderFrontLoadingCertification.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ReorderExtremalitySignFlip
/-
# Front-loading, the touch floor, and lab certification of the prior-shape channel

Third instalment of the GAP-L7' programme
(`Novelty.ReorderExtremalitySignFlip`, `Novelty.ReorderMasterCapWitnesses`).
It closes three of the ranked ledger items with unconditional statements.

## L7-c : the touch floor, proved rather than booked

* `cost_eq_tail_sums` — the Abel identity `∑ (k+1)·w k = ∑_j tail_j(w)`: the
  expected probe cost of an enumeration is the sum of its *survival* masses.
* `frontload_le` — **head-domination law**: if one order's prefix masses dominate
  another's (it front-loads more), its expected cost is smaller.  This is the
  only thing that transfers from the exp-570 early-fire trace — *front-loading*,
  not `√N`-descending dominance.
* `uniform_scan_cost`, `speedup_le_inv_mu` — the touch floor: a policy that must
  still touch a `μ`-fraction of the index set pays at least `(μM+1)/2` probes, so
  its speedup against the full scan is at most `1/μ`.  The `1/μ` branch of the
  master cap is therefore a theorem, not a booking.

## L7-a : lab certification of `Λ` from a measured mean with error bars

* `asc_lt_desc_iff_mean` — the scalar sign-flip criterion.
* `Lambda_lab`, `Lambda_antitone`, `Lambda_bracket` — the prior-shape gain
  `Λ = (1 - m)/(m - 1/√2)` is strictly antitone in the population mean
  `m = E[1/√r]`, so a measurement `m̂ ± ε` brackets `Λ` between
  `Λ(m̂+ε)` and `Λ(m̂-ε)`.
* `signflip_certified` — a measurement certifies the winner as soon as the error
  bar clears the crossover: `m̂ + ε < (2+√2)/4` forces window-ascending to win.
  This is exactly the missing step L7-a: without a measured `Λ_lab` the premise
  is unchecked, with one the conclusion is unconditional.

## No free lunch on flat priors

* `flat_prior_cost` — against a flat population every enumeration costs the same
  `(n+1)/2`.  All REORDER gains are therefore prior-shape gains; a policy cannot
  manufacture one, which is the structural reason the residue-coupling arms of
  the ledger measured exactly zero.

-- !-- Lab Notes -- !--
-- With the round-74 hard-balanced measurement m̂ ≈ 0.8284 (tilt 0.4095-0.4148,
-- analytic √2 - 1) and a conservative ε = 0.01, `signflip_certified` applies:
-- 0.8384 < (2+√2)/4 = 0.85355, so window-ascending is certified extremal on
-- that pool, and `Lambda_bracket` brackets the gain factor Λ.
-- On the narrow-band pool (m̂ ≈ 0.899) the same test fires the other way.
-/

namespace ReorderL7

open Finset

noncomputable section

/-! ## 1.  Abel identity and the head-domination law -/

/-- Expected probe cost of the enumeration whose `k`-th probe carries mass `w k`. -/
def scanCostOf (n : ℕ) (w : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range n, ((k : ℝ) + 1) * w k



/-! ## 2.  No free lunch on a flat prior -/



/-! ## 3.  The touch floor : the `1/μ` branch is a theorem -/



/-! ## 4.  L7-a : certifying the prior-shape channel from a lab measurement -/


/-- The prior-shape gain factor `Λ_lab` read off a measured population mean
`m = E[1/√r]`: the ratio of the descending cost to the ascending cost. -/
def Lambda_lab (m : ℝ) : ℝ := (1 - m) / (m - 1 / Real.sqrt 2)





end

end ReorderL7


