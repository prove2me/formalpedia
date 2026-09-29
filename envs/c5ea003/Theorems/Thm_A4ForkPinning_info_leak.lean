-- Prove2me | Theorems.Thm_A4ForkPinning_info_leak
-- name    : A4ForkPinning.info_leak
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:25:36.217317+00:00
-- url     : https://prove2.me/theorems/37522a55-a4c4-4a9a-84a8-d091c5179c49
-- title:
--   Exact leakage law.
-- statement:
--   **Exact leakage law.**  Let `g` be a pinned fork of rate `p` and let `F` be the
--   `q`-thinning of `g` (i.e. `P(F = 1 | dial = y) = q · g y`).  Then
--
--   `I(dial ; F) = H(pq) - p · H(q)`.
--
--   For `q = 1` this degenerates to the pinned law `I = H(p)`; for `p = 1` to flatness.
--
--   ```lean
--   theorem A4ForkPinning.info_leak(w g : Y → ℝ) (q : ℝ) (hg : ∀ y, g y = 0 ∨ g y = 1) :
--       info w (fun y => q * g y) = hb (q * avg w g) - avg w g * hb q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/A4ForkPinning/Information.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/A4ForkPinning/Information.lean#L182

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

theorem A4ForkPinning.info_leak(w g : Y → ℝ) (q : ℝ) (hg : ∀ y, g y = 0 ∨ g y = 1) :
    info w (fun y => q * g y) = hb (q * avg w g) - avg w g * hb q := by sorry
