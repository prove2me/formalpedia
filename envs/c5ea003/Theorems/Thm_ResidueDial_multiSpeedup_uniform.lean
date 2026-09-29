-- Prove2me | Theorems.Thm_ResidueDial_multiSpeedup_uniform
-- name    : ResidueDial.multiSpeedup_uniform
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:58:36.7285+00:00
-- url     : https://prove2.me/theorems/4f0dd648-f524-42e8-9c3c-2ed19ce8a709
-- title:
--   Uniform blocks attain the cap exactly.
-- statement:
--   Uniform blocks attain the cap exactly.
--
--   ```lean
--   theorem ResidueDial.multiSpeedup_uniform{r : ℕ} (hr : 0 < r) :
--       multiSpeedup (fun _ : Fin r => (1 : ℝ) / r) = 2 * r / ((r : ℝ) + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ResidueDial/MultiSymbol.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ResidueDial/MultiSymbol.lean#L127

-- Thm stub generated from Cryptography/ResidueDial/MultiSymbol.lean
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

theorem ResidueDial.multiSpeedup_uniform{r : ℕ} (hr : 0 < r) :
    multiSpeedup (fun _ : Fin r => (1 : ℝ) / r) = 2 * r / ((r : ℝ) + 1) := by sorry
