-- Prove2me | Definitions.Def_Cryptography_ResidueDial_MultiSymbol
-- name    : Cryptography_ResidueDial_MultiSymbol
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:23:15.884666+00:00
-- url     : https://prove2.me/theorems/10b5e723-5607-45cd-b961-be08d5e6d859
-- title:
--   Aether Catalog definitions — Cryptography_ResidueDial_MultiSymbol
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ResidueDial.MultiSymbol`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ResidueDial/MultiSymbol.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Core

/-!
# Multi-symbol dials: the hierarchy of caps `2r/(r+1)`

A binary dial splits the class space into two blocks (kept / rejected) and is
capped at `4/3`.  An `r`-symbol dial splits it into `r` blocks, scanned in some
order; the scan pays, for a target in the `i`-th block, everything up to and
including that block.  Its normalised cost is

  `prefixCost θ = Σ_i θ_i (θ_1 + … + θ_i)`.

Three facts are proved here.

* `two_mul_prefixCost` — the **order-free identity**
  `2 · prefixCost θ = (Σ θ)² + Σ θ²`.  In particular the cost does not depend on
  the order in which the blocks are scanned (`prefixCost_comp_perm`): there is
  no clever ordering to find, contrary to what one might expect from a
  rearrangement heuristic.
* `multiSpeedup_le_cap` — the **cap hierarchy**: for a dial with `r` blocks,
  `Speedup ≤ 2r/(r+1)`, attained exactly at uniform blocks
  (`multiSpeedup_uniform`).  At `r = 2` this is the `4/3` of `Core.lean`
  (`prefixCost_two_eq_dialCost`, `cap_two_eq_four_thirds`).
* `cap_lt_two`, `cap_tendsto_two` — the hierarchy is strictly below `2` and
  converges to it: the asked barrier `2` is the `r → ∞` limit of the
  multi-symbol caps, never a value.
-/

namespace ResidueDial

open Finset

/-- Normalised cost of a scan through `r` blocks of densities `θ`: a target in
block `i` costs the total density of blocks `1 … i`. -/
noncomputable def prefixCost {r : ℕ} (θ : Fin r → ℝ) : ℝ :=
  ∑ i, θ i * ∑ j ∈ univ.filter (fun j => j ≤ i), θ j

/-- Speedup of an `r`-block dial. -/
noncomputable def multiSpeedup {r : ℕ} (θ : Fin r → ℝ) : ℝ := 1 / prefixCost θ










/-! ## Boundary: what would break the cap

The cap `2r/(r+1)` — and with it the `4/3` of `Core.lean` — is a statement about
*single-pass scans*: the dial reorders the blocks, but a block once scheduled is
paid for.  If instead the dial's answer lets the algorithm **skip** the blocks it
has ruled out, the cost is `Σ θ²` and the cap disappears: a balanced `r`-symbol
full reveal buys exactly `r`.  This is the precise boundary of the converse, and
it is where the barrier-`2` framing of the binary case comes from
(`revealSpeedup_binary_half`). -/

/-- Cost of a *full-reveal* dial: the answer names the target's block and the
algorithm scans that block only. -/
noncomputable def revealCost {r : ℕ} (θ : Fin r → ℝ) : ℝ := ∑ i, (θ i) ^ 2





end ResidueDial


