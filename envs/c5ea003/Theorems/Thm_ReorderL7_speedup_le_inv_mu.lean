-- Prove2me | Theorems.Thm_ReorderL7_speedup_le_inv_mu
-- name    : ReorderL7.speedup_le_inv_mu
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:28:58.203847+00:00
-- url     : https://prove2.me/theorems/3b7ef28a-c536-4f4b-9c63-a3079e96962c
-- title:
--   Touch floor ⇒ the `1/μ` branch of the master cap.
-- statement:
--   **Touch floor ⇒ the `1/μ` branch of the master cap.**  If the filter still
--   keeps at least a `μ`-fraction of the `M` candidates, the policy pays at least
--   `(μM+1)/2` probes, so its speedup against the full scan `(M+1)/2` is at most
--   `1/μ`.  No booking, no uniformity assumption inside cells.
--
--   ```lean
--   theorem ReorderL7.speedup_le_inv_mu{M k : ℕ} {mu : ℝ} (hmu : 0 < mu) (hmu1 : mu ≤ 1)
--       (hk : mu * (M : ℝ) ≤ (k : ℝ)) :
--       (((M : ℝ) + 1) / 2) / (((k : ℝ) + 1) / 2) ≤ 1 / mu := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ReorderFrontLoadingCertification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ReorderFrontLoadingCertification.lean#L126

-- Thm stub generated from Novelty/ReorderFrontLoadingCertification.lean
import Mathlib
import Definitions.Def_Novelty_ReorderExtremalitySignFlip
import Definitions.Def_Novelty_ReorderFrontLoadingCertification
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

open ReorderL7

open Finset

noncomputable section

/-! ## 1.  Abel identity and the head-domination law -/




/-! ## 2.  No free lunch on a flat prior -/



/-! ## 3.  The touch floor : the `1/μ` branch is a theorem -/

theorem ReorderL7.speedup_le_inv_mu{M k : ℕ} {mu : ℝ} (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hk : mu * (M : ℝ) ≤ (k : ℝ)) :
    (((M : ℝ) + 1) / 2) / (((k : ℝ) + 1) / 2) ≤ 1 / mu := by sorry
