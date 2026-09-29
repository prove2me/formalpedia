-- Prove2me | solution 1 for ResidueDial.cap_tendsto_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:44:28.813043+00:00
-- url     : https://prove2.me/submissions/6864cefa-eb1a-4536-8580-1a757ad7d1ed

-- Sol generated from Cryptography/ResidueDial/MultiSymbol.lean
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Core
import Definitions.Def_Cryptography_ResidueDial_MultiSymbol

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

open ResidueDial

open Finset












/-! ## Boundary: what would break the cap

The cap `2r/(r+1)` — and with it the `4/3` of `Core.lean` — is a statement about
*single-pass scans*: the dial reorders the blocks, but a block once scheduled is
paid for.  If instead the dial's answer lets the algorithm **skip** the blocks it
has ruled out, the cost is `Σ θ²` and the cap disappears: a balanced `r`-symbol
full reveal buys exactly `r`.  This is the precise boundary of the converse, and
it is where the barrier-`2` framing of the binary case comes from
(`revealSpeedup_binary_half`). -/







open ResidueDial in
theorem solution:
    Filter.Tendsto (fun r : ℕ => 2 * (r : ℝ) / ((r : ℝ) + 1)) Filter.atTop (nhds 2) := by
  have h : ∀ r : ℕ, 2 * (r : ℝ) / ((r : ℝ) + 1) = 2 - 2 / ((r : ℝ) + 1) := by
    intro r
    have hr : ((r : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  simp only [h]
  have h0 : Filter.Tendsto (fun r : ℕ => 1 / ((r : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Filter.Tendsto (fun r : ℕ => 2 / ((r : ℝ) + 1)) Filter.atTop (nhds 0) := by
    have := h0.const_mul (2:ℝ)
    simpa [mul_one_div] using this
  simpa using (tendsto_const_nhds (x := (2:ℝ)) (f := Filter.atTop (α := ℕ))).sub h2
