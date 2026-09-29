-- Prove2me | solution 1 for ResidueDial.multiSpeedup_uniform
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:52:40.777354+00:00
-- url     : https://prove2.me/submissions/ef09d7c2-62e4-45f9-a912-df72f4235cd9

-- Sol generated from Cryptography/ResidueDial/MultiSymbol.lean
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Core
import Definitions.Def_Cryptography_ResidueDial_MultiSymbol
import Theorems.Thm_ResidueDial_two_mul_prefixCost

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





/-- With total density `1`, the cost is `(1 + Σθ²)/2`. -/
theorem prefixCost_of_sum_one {r : ℕ} {θ : Fin r → ℝ} (h : ∑ i, θ i = 1) :
    prefixCost θ = (1 + ∑ i, (θ i) ^ 2) / 2 := by
  have := two_mul_prefixCost θ
  rw [h] at this
  linarith







/-! ## Boundary: what would break the cap

The cap `2r/(r+1)` — and with it the `4/3` of `Core.lean` — is a statement about
*single-pass scans*: the dial reorders the blocks, but a block once scheduled is
paid for.  If instead the dial's answer lets the algorithm **skip** the blocks it
has ruled out, the cost is `Σ θ²` and the cap disappears: a balanced `r`-symbol
full reveal buys exactly `r`.  This is the precise boundary of the converse, and
it is where the barrier-`2` framing of the binary case comes from
(`revealSpeedup_binary_half`). -/







open ResidueDial in
theorem solution{r : ℕ} (hr : 0 < r) :
    multiSpeedup (fun _ : Fin r => (1 : ℝ) / r) = 2 * r / ((r : ℝ) + 1) := by
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hsum : ∑ _i : Fin r, (1 : ℝ) / r = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hsq : ∑ _i : Fin r, ((1 : ℝ) / r) ^ 2 = 1 / r := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hcost : prefixCost (fun _ : Fin r => (1 : ℝ) / r) = ((r : ℝ) + 1) / (2 * r) := by
    rw [prefixCost_of_sum_one hsum, hsq]
    field_simp
  rw [multiSpeedup, hcost, one_div_div]
