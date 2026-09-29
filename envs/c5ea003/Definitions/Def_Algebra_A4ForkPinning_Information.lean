-- Prove2me | Definitions.Def_Algebra_A4ForkPinning_Information
-- name    : Algebra_A4ForkPinning_Information
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:03:51.600489+00:00
-- url     : https://prove2.me/theorems/d8d6c2d1-20a0-40af-b29f-efde43893be5
-- title:
--   Aether Catalog definitions — Algebra_A4ForkPinning_Information
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.A4ForkPinning.Information`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/A4ForkPinning/Information.lean by skeleton subtraction
import Mathlib
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

namespace A4ForkPinning

open Real Finset Set

/-! ## Bit-valued entropy -/

/-- `nml x = -x log₂ x`, the entropy contribution of a single outcome, in bits. -/
noncomputable def nml (x : ℝ) : ℝ := Real.negMulLog x / Real.log 2

/-- Binary entropy in bits, `H(x) = -x log₂ x - (1-x) log₂ (1-x)`. -/
noncomputable def hb (x : ℝ) : ℝ := nml x + nml (1 - x)

/-- Shannon entropy (in bits) of a finitely supported distribution. -/
noncomputable def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ := ∑ i, nml (p i)













/-! ## Concavity -/




/-! ## The dial → fork channel -/

variable {Y : Type*} [Fintype Y]

/-- The unconditional rate `P(F = 1) = ∑_y w y · f y` of a fork with conditional
rates `f` on a dial with weights `w`. -/
noncomputable def avg (w f : Y → ℝ) : ℝ := ∑ y, w y * f y

/-- Conditional entropy `H(F | dial)` in bits. -/
noncomputable def condEntropy (w f : Y → ℝ) : ℝ := ∑ y, w y * hb (f y)

/-- Mutual information `I(dial ; F) = H(F) - H(F | dial)` in bits. -/
noncomputable def info (w f : Y → ℝ) : ℝ := hb (avg w f) - condEntropy w f

/-- Mutual information between a dial and an arbitrary finite-valued observable
given by conditional distributions `P y`. -/
noncomputable def infoGen {Z : Type*} [Fintype Z] (w : Y → ℝ) (P : Y → Z → ℝ) : ℝ :=
  entropy (fun z => ∑ y, w y * P y z) - ∑ y, w y * entropy (P y)

  -- `simp only` above already closes the goal

/-! ### Pinned forks -/


/-! ### Flat forks -/


/-! ### Leaking forks -/



/-! ### The trichotomy -/




end A4ForkPinning


