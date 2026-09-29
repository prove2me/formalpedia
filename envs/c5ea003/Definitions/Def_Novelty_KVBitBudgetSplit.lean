-- Prove2me | Definitions.Def_Novelty_KVBitBudgetSplit
-- name    : Novelty_KVBitBudgetSplit
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:40:26.20889+00:00
-- url     : https://prove2.me/theorems/64113e48-c7f3-4506-a23a-6f5713303d65
-- title:
--   Aether Catalog definitions — Novelty_KVBitBudgetSplit
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KVBitBudgetSplit`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KVBitBudgetSplit.lean by skeleton subtraction
import Mathlib

/-!
# Splitting the cache budget by role: depth amplification and the optimal bit split

Cycle 3 of the NET-93 thread.  `Novelty.KeysOwnTheCliff` and
`Novelty.KVCliffExponent` establish the *per-layer* asymmetry: value error is
`1`-Lipschitz, key error is amplified by the query norm and then exponentiated.
Two consequences remain to be proved.

**Depth.**  The key path is the recursion the NET-83 note calls "amplifying":
each layer multiplies the perturbation by a factor `γ > 1`.  The value path is
an averaging recursion, which is non-expansive.  Sections 1–2 prove that these
two recursions have qualitatively different fates: `key_error_unbounded_in_depth`
(the key error passes every threshold at some depth) versus
`value_error_stays_le` (the value error never leaves its initial band).

**Budget.**  Section 3 studies the deployment question directly.  With the
first-order damage model `damage A bK bV = A/2^bK + 1/2^bV` — key damage carries
the amplification factor `A`, value damage does not —

* `shift_bit_to_keys` — moving one bit from the values to the keys *strictly*
  reduces damage whenever `2^bK < A · 2^bV`;
* `shift_bit_to_values_not_better` — and not otherwise, so the inequality
  `2^bK < A · 2^bV` characterises the equilibrium;
* `k8v4_optimal` — at the measured asymmetry scale `A = 16` and a 12-bit budget
  the unique optimum is **K8/V4**, the arm NET-93 nominates as the immediate
  follow-up.  In particular `k8v4_beats_symmetric`: K8/V4 strictly beats the
  equal split K6/V6 at the same average of 6 bits per element.

All of Section 3 is exact rational arithmetic — no floating point, no rounding.
-/

namespace Catalog.Novelty.KVBitBudgetSplit


/-! ### 1. The key path: geometric amplification through depth -/



/-! ### 2. The value path: an averaging recursion never leaves its band -/



/-! ### 3. The bit budget: keys deserve the bits -/

/-- First-order damage model for a `bK`-bit key cache and a `bV`-bit value
cache: the key term carries the amplification factor `A`, the value term does
not.  Exact rational arithmetic. -/
def damage (A : ℚ) (bK bV : ℕ) : ℚ := A / 2 ^ bK + 1 / 2 ^ bV






end Catalog.Novelty.KVBitBudgetSplit


