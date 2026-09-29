-- Prove2me | Definitions.Def_Tropical_Barrier4FixedWindowOracle
-- name    : Tropical_Barrier4FixedWindowOracle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:25.86525+00:00
-- url     : https://prove2.me/theorems/c886f6a6-b364-4508-979e-213a417df6f8
-- title:
--   Aether Catalog definitions — Tropical_Barrier4FixedWindowOracle
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.Barrier4FixedWindowOracle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/Barrier4FixedWindowOracle.lean by skeleton subtraction
import Mathlib

/-!
# Barrier-4 positional converse, stratum T1: the fixed-window oracle

This file formalises the **T1 (fixed-window oracle)** stratum of the barrier-4 positional /
magnitude converse.  The setting is the min-plus ("tropical") search picture used throughout the
factor-location barrier thread (`Tropical.FactorLocationBarriers`): the search space is normalised
to total measure `1`, a *block* `B` of relative measure `μ` is singled out by an oracle, and the
cost of an algorithm is the expected relative measure it must scan.  The **speedup** of a protocol
is `S = 1 / cost`.

The oracle *hits* with probability `P` (`P = P_hit`).  Three laws are in play.

* `costCert μ P = μ·P + (1−P)·(1−μ)` — the **certified-silence law**: silence is a certificate
  that the target is outside the block, so a silent oracle costs only the complement.
* `costFireOrSilent μ P = 1 − (1−μ)·P` — the **drafted fire-or-silent law**: silence carries no
  certificate, so the whole space must be re-scanned.
* `costRescan μ P = μ + (1−P)` — **protocol B**, block-first with a wasteful full re-scan on miss.

The main results:

* `cost_arithmetic_progression` : the three laws are in arithmetic progression with common gap
  `μ(1−P)`; in particular the drafted law is *superseded* — it strictly understates the certified
  speedup whenever `μ > 0` and `P < 1` (`speedup_drafted_lt_speedup_cert`).
* `speedupB_le_speedupA` : protocol B never beats protocol A.
* `costCert_ge_mu` / `speedupCert_le_inv_mu` : the cap `S_A ≤ 1/μ`, **valid only for `μ ≤ 1/2`**
  and attained exactly at `P = 1` (`speedupCert_at_hit_one`).  The restriction is sharp:
  `speedupCert_gt_inv_mu_of_large_block` exhibits `μ = 9/10, P = 0` with `S_A = 10 > 1/μ`.
* `no_constant_cap` : no constant bounds the certified speedup.
* `costCert_half_block_const` : at `μ = 1/2` the certified speedup is exactly `2`, *independently*
  of `P` — the oracle's information is worthless at the balanced block.
* `blockFirst_dominance_A` : block-first dominance is **unconditional** for protocol A;
* `blockFirst_dominance_B_iff` : for protocol B it holds **iff `μ ≤ P`** — every counterexample
  has `P < μ`, exactly as the finite sweeps reported.
-/

namespace Barrier4

/-! ## 1. The three cost laws -/

/-- Protocol A, committed policy: **certified silence**.  With probability `P` the oracle fires
and the block (measure `μ`) is scanned; with probability `1−P` silence certifies that the target
lies in the complement (measure `1−μ`). -/
def costCert (mu P : ℝ) : ℝ := mu * P + (1 - P) * (1 - mu)

/-- The drafted (superseded) **fire-or-silent** law: silence certifies nothing, so the entire
space is scanned. -/
def costFireOrSilent (mu P : ℝ) : ℝ := 1 - (1 - mu) * P

/-- Protocol B, block-first: pay the block, and on a miss re-scan the whole space. -/
def costRescan (mu P : ℝ) : ℝ := mu + (1 - P)

/-- Protocol B, complement-first. -/
def costRescanComp (mu P : ℝ) : ℝ := (1 - mu) + P

/-- Protocol A, complement-first: when the oracle fires the complement scan is pure waste. -/
def costCertComp (mu P : ℝ) : ℝ := P + (1 - P) * (1 - mu)

/-- Speedup relative to the exhaustive scan of cost `1`. -/
noncomputable def speedup (c : ℝ) : ℝ := 1 / c

/-! ## 2. Positivity of the certified cost -/


/-! ## 3. The three laws form an arithmetic progression -/






/-! ## 4. The cap `1/μ`, its regime, and the absence of a constant cap -/









/-! ## 5. Block-first dominance -/





/-! ## 6. The uninformative point -/



end Barrier4


