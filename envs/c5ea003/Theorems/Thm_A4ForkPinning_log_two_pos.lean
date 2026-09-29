-- Prove2me | Theorems.Thm_A4ForkPinning_log_two_pos
-- name    : A4ForkPinning.log_two_pos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:25:22.880422+00:00
-- url     : https://prove2.me/theorems/82b2641b-a074-4e3c-9c2a-37c36c4234c9
-- title:
--   Log two pos
-- statement:
--   Formal statement of `A4ForkPinning.log_two_pos` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem A4ForkPinning.log_two_pos: 0 < Real.log 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/A4ForkPinning/Information.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/A4ForkPinning/Information.lean#L44

-- Thm stub generated from Algebra/A4ForkPinning/Information.lean
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_Information
/-
# Fork information: the pinned / flat / leaking trichotomy

Formal core of the *A4-FORK-PINNING* experiment (paper 75, experiment 410).

A **fork** attached to a number field is a binary observable `F` of the Frobenius
class of a prime `p`; a **dial** is a residue datum `y = p mod m`.  The
experiment measures the mutual information `I(y ; F)` and observes exactly three
regimes:

* **pinned**   — `F` is a function of `y`, and `I = H(F)` is maximal;
* **flat**     — `F` is independent of `y`, and `I = 0`;
* **leaking**  — `F` is a *thinning* of a pinned event, and `0 < I < H(F)`,
  with the exact closed form `I = H(pq) - p·H(q)`.

This file builds the (bit-valued) information calculus needed to state and prove
those three laws for an arbitrary finite dial:

* `A4ForkPinning.info_of_pinned`   — pinned forks realise `I = H(F)`;
* `A4ForkPinning.info_of_flat`     — flat forks realise `I = 0`;
* `A4ForkPinning.info_leak`        — the **exact leakage law** `I = H(pq) - p·H(q)`;
* `A4ForkPinning.info_leak_strict` — leakage is strictly between the two regimes;
* `A4ForkPinning.info_trichotomy`  — `0 ≤ I ≤ H(F)`, with `I = 0` iff the fork is
  flat and `I = H(F)` iff the fork is pinned (strict Jensen in both directions).

All entropies are measured in **bits** (`negMulLog` divided by `log 2`).
-/

open A4ForkPinning

open Real Finset Set

/-! ## Bit-valued entropy -/

theorem A4ForkPinning.log_two_pos: 0 < Real.log 2 := by sorry
