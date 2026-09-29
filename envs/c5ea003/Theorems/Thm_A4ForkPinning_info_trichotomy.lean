-- Prove2me | Theorems.Thm_A4ForkPinning_info_trichotomy
-- name    : A4ForkPinning.info_trichotomy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:26:08.687462+00:00
-- url     : https://prove2.me/theorems/fc8730ac-191d-4a3e-8ad8-2fd36f59353b
-- title:
--   Fork trichotomy.
-- statement:
--   **Fork trichotomy.**  For a strictly positive dial distribution:
--   `I ≥ 0`, with `I = 0` exactly for flat forks, and `I ≤ H(F)`, with equality exactly
--   for pinned forks.  Everything else leaks: `0 < I < H(F)`.
--
--   ```lean
--   theorem A4ForkPinning.info_trichotomy(w f : Y → ℝ) [Nonempty Y] (hw : ∀ y, 0 < w y) (hsum : ∑ y, w y = 1)
--       (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1) :
--       0 ≤ info w f ∧ info w f ≤ hb (avg w f) ∧
--         (info w f = 0 ↔ ∀ y y', f y = f y') ∧
--         (info w f = hb (avg w f) ↔ ∀ y, f y = 0 ∨ f y = 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/A4ForkPinning/Information.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/A4ForkPinning/Information.lean#L241

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
















/-! ## Concavity -/




/-! ## The dial → fork channel -/

variable {Y : Type*} [Fintype Y]





  -- `simp only` above already closes the goal

/-! ### Pinned forks -/


/-! ### Flat forks -/


/-! ### Leaking forks -/



/-! ### The trichotomy -/

theorem A4ForkPinning.info_trichotomy(w f : Y → ℝ) [Nonempty Y] (hw : ∀ y, 0 < w y) (hsum : ∑ y, w y = 1)
    (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1) :
    0 ≤ info w f ∧ info w f ≤ hb (avg w f) ∧
      (info w f = 0 ↔ ∀ y y', f y = f y') ∧
      (info w f = hb (avg w f) ↔ ∀ y, f y = 0 ∨ f y = 1) := by sorry
