-- Prove2me | Theorems.Thm_ResidueDial_totient_pos_of_neZero
-- name    : ResidueDial.totient_pos_of_neZero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:58:02.729013+00:00
-- url     : https://prove2.me/theorems/510ada05-a08b-4e18-ae5a-727f66019a0d
-- title:
--   Totient pos of neZero
-- statement:
--   Formal statement of `ResidueDial.totient_pos_of_neZero` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ResidueDial.totient_pos_of_neZero(M : ℕ) [NeZero M] : 0 < M.totient := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/ResidueDial/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/ResidueDial/Core.lean#L233

-- Thm stub generated from Cryptography/ResidueDial/Core.lean
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Core

/-!
# The residue-dial speedup law and the universal cap `4/3`

A *residue dial* is the simplest conceivable oracle that a factoring scan can be
handed: a modulus `M`, a set `K` of residue classes modulo `M`, and the promise
that the sought factor's class lies in `K` or does not.  Empirically (paper 88)
the best speedup such a filter can buy a scanning algorithm follows a fixed
curve in the *density* `θ = |K| / φ(M)` alone.  This file turns that empirical
curve into a theorem for the whole congruence stratum.

## The model

The scan has `n = φ(M)` admissible residue classes; the target class `t` is
uniform among them.  The dial-aware algorithm scans the `k = |K|` kept classes
first and, if the target is not there, is forced back onto the full scan.  Its
cost on target `t` is therefore

  `cost t = if t ∈ K then k else n`,

whose average over `t` is `expectedScanCost`.  Normalising by the baseline `n`
gives the *exact law*

  `expectedScanCost / n = 1 - θ + θ²`,  `Speedup = 1 / (1 - θ + θ²)`.

## Scope (read this before quoting the constant)

The model is a *single-pass scan*: the dial reorders the candidate classes, but a
class once scheduled is paid for.  If the dial's answer instead lets the
algorithm **skip** the rejected classes outright, the cost is `Σ θᵢ²` and no
universal cap holds — a balanced `r`-symbol full reveal then buys exactly `r`
(`ResidueDial.revealSpeedup_uniform` in `MultiSymbol.lean`).  So `4/3` is a
theorem about scan-order algorithms, not about arbitrary use of congruence
information; `Accounting.lean` and `MultiSymbol.lean` chart the boundary.

## Main results

* `expectedScanCost_eq` — Claim A: the exact law, derived from the finite model
  by summation, for an arbitrary filter `K` in an arbitrary finite class space.
* `dialCost_ge_three_quarters`, `speedup_le_four_thirds` — the **universal cap**
  `Speedup ≤ 4/3`, with equality exactly at `θ = 1/2`
  (`speedup_eq_four_thirds_iff`).
* `speedup_lt_two` — the barrier-4 converse in the asked form: a residue dial
  can never buy a factor-`2` speedup.
* `speedup_of_trivial` — trivial filters (`θ = 0`, `θ = 1`) buy exactly `1`.
* `speedup_strictMonoOn`, `speedup_strictAntiOn`, `isGreatest_speedup` — the
  shape of the curve and that `4/3` really is the maximum over `θ ∈ [0,1]`.
* `dialSpeedup_le_four_thirds` and `exists_dial_speedup_eq_four_thirds` — the
  cap and its attainment for genuine residue dials `K ⊆ (ZMod M)ˣ`; the
  attaining sets are *arbitrary* half-density sets, no character structure is
  required (Lemma B2, see `Converse.lean`).

Everything below depends on `K` only through its cardinality; that is the
content of the structure-blindness corollaries collected in `Converse.lean`.
-/

open ResidueDial

open Finset

/-! ## The law -/




















/-! ## Claim A: deriving the law from the finite scan model -/

variable {α : Type*} [Fintype α] [DecidableEq α]







/-! ## Genuine residue dials -/

theorem ResidueDial.totient_pos_of_neZero(M : ℕ) [NeZero M] : 0 < M.totient := by sorry
