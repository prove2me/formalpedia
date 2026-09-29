-- Prove2me | Theorems.Thm_GenericRecovery_card_image_sqHint
-- name    : GenericRecovery.card_image_sqHint
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:18:34.388139+00:00
-- url     : https://prove2.me/theorems/91c33377-9b99-4f3a-b400-6744fe8f10ba
-- title:
--   The `t`-bit trace hint carries only `t-3` bits.
-- statement:
--   **The `t`-bit trace hint carries only `t-3` bits.**  With `t = n+3`, the
--   square hint (the content of a trace hint `s = p+q mod 2^t`, after completing the
--   square) realises exactly `2^{t-3}` distinct readings on the `2^{t-1}` odd
--   residues.  One bit is lost to parity, two to the square-root ambiguity.
--
--   ```lean
--   theorem GenericRecovery.card_image_sqHint(n : ℕ) :
--       #((oddResidues n).image (fun x => x ^ 2 % 2 ^ (n + 3))) = 2 ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/GenericRecoveryHintSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/GenericRecoveryHintSharpness.lean#L196

-- Thm stub generated from Combinatorics/GenericRecoveryHintSharpness.lean
import Mathlib
import Definitions.Def_Combinatorics_DialThresholdNoAmplification
import Definitions.Def_Combinatorics_GenericRecoveryHintSharpness
import Definitions.Def_Combinatorics_GenericRecoveryHintTaxonomy
/-
# GENERIC-RECOVERY, cycle II: the taxonomy is *tight*

Sequel to `Combinatorics.GenericRecoveryHintTaxonomy`.  Cycle I proved the
negative half of the hint taxonomy: a `t`-bit hint never cuts a candidate set by
more than `2^t`, parity-constrained value hints lose a bit, post-processing and
joining never help, and public hints are worthless.  A negative theory is only
as strong as its sharpness, and only as interesting as the *exact* deficit it
assigns to the borderline families.  This file supplies three sharpenings and
one bridge.

* **§1 Sharpness.**  `GenericRecovery.card_fiber_blockHint` and
  `GenericRecovery.image_blockHint`: on a candidate set of size `q·2^t` the
  block hint `p ↦ p / q` realises all `2^t` values with *every* fibre of size
  exactly `q = |S| / 2^t`.  Together with the master bound of cycle I, the
  reduction factor of a `t`-bit hint is exactly `2^t` — never more (cycle I),
  and attained (here).  Hints are worth their bits at face value.
* **§2 Average case, not just worst case.**
  `GenericRecovery.sq_sum_cost_ge`: by Cauchy–Schwarz, the *expected* number of
  candidates the adversary must scan (over the induced distribution of hint
  readings) is at least `|S| / 2^t`.  The experiment measured medians equal to
  the class size; this is the theorem behind that observation, and it rules out
  a hint whose typical class is small while a few classes soak up the mass.
* **§3 The trace/square hint is worth `t - 3` bits, exactly.**
  `GenericRecovery.card_natSqFiber` (every fibre of `p ↦ p² mod 2^t` on the odd
  residues has exactly 4 elements) and
  `GenericRecovery.card_image_sqHint` (the hint therefore realises exactly
  `2^{t-3}` values).  A `t`-bit trace hint carries `t-3` usable bits: one bit to
  parity (§3 of cycle I), two bits to the square-root ambiguity.  This is the
  measured `log₂ C_t ≈ 3` deficit, now a theorem.
* **§4 Bridge to DIAL-THRESHOLD.**  `GenericRecovery.worstCost_dialVec_ge`:
  a residue-dial system is a hint of `log₂ (M*/gcd(M*,m))` bits and therefore
  obeys the master bound.  The two negative programmes are one programme.
-/

open GenericRecovery

open Finset

/-! ## 1.  Sharpness: the block hint attains the master bound exactly -/






/-! ## 2.  The average class is large too (Cauchy–Schwarz) -/

variable {α β : Type*} [DecidableEq β]



/-! ## 3.  The trace hint is worth exactly `t - 3` bits -/

theorem GenericRecovery.card_image_sqHint(n : ℕ) :
    #((oddResidues n).image (fun x => x ^ 2 % 2 ^ (n + 3))) = 2 ^ n := by sorry
