-- Prove2me | solution 1 for ResidueDial.exists_dial_speedup_eq_four_thirds
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:48:46.314791+00:00
-- url     : https://prove2.me/submissions/b110418e-5002-4bea-9dcf-c3fcf3a77202

-- Sol generated from Cryptography/ResidueDial/Core.lean
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Core
import Theorems.Thm_ResidueDial_speedup_eq_four_thirds_iff
import Theorems.Thm_ResidueDial_totient_pos_of_neZero

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








open ResidueDial in
theorem solution(M : ℕ) [NeZero M] (h : Even M.totient) :
    ∃ K : Finset (ZMod M)ˣ, speedup (density M K) = 4 / 3 := by
  obtain ⟨m, hm⟩ := h
  have hcard : Fintype.card (ZMod M)ˣ = M.totient := ZMod.card_units_eq_totient M
  have hle : m ≤ (univ : Finset (ZMod M)ˣ).card := by
    rw [Finset.card_univ, hcard, hm]; omega
  obtain ⟨K, -, hK⟩ := Finset.exists_subset_card_eq hle
  refine ⟨K, speedup_eq_four_thirds_iff.mpr ?_⟩
  have hMpos : 0 < M.totient := totient_pos_of_neZero M
  have hne : (M.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hMpos.ne'
  have hm0 : 0 < m := by omega
  have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hmR : ((m : ℝ) + m) ≠ 0 := ne_of_gt (by linarith)
  rw [density, hK, hm]
  push_cast
  rw [div_eq_div_iff hmR (by norm_num : (2:ℝ) ≠ 0)]
  ring
