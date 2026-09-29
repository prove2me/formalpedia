-- Prove2me | Theorems.Thm_SpikeOrigin_midRegime_fullsize_witness
-- name    : SpikeOrigin.midRegime_fullsize_witness
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:01:56.683824+00:00
-- url     : https://prove2.me/theorems/ac5456fd-9278-40d8-b590-647afd7cc15c
-- title:
--   First witness: `N₁ = (2⁴⁸ − 1)²` is a `96`-bit modulus, and at normalised position
-- statement:
--   First witness: `N₁ = (2⁴⁸ − 1)²` is a `96`-bit modulus, and at normalised position
--   `u = (j − s)/(2s) ≤ 0.15` the residue is already **full size** (`≥ 2⁹⁵`).
--
--   ```lean
--   theorem SpikeOrigin.midRegime_fullsize_witness:
--       ∃ N j : ℕ, 2 ^ 95 ≤ N ∧ N < 2 ^ 96 ∧ Nat.sqrt N < j ∧ j ≤ 3 * Nat.sqrt N ∧
--         100 * (j - Nat.sqrt N) ≤ 15 * (2 * Nat.sqrt N) ∧ 2 ^ 95 ≤ resid N j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/SpikeOriginBands.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/SpikeOriginBands.lean#L95

-- Thm stub generated from Cryptography/SpikeOriginBands.lean
import Mathlib
import Definitions.Def_Cryptography_SpikeOriginDegeneracy
/-
# Band structure of the Fermat-window residues: the left-edge spike is not one object

Companion to `Cryptography.SpikeOriginDegeneracy`.  Three results:

* `firstDecile_size_lt_size` — a **scale-free** band statement: for every modulus
  `N ≥ 2¹⁶`, a first-decile residue satisfies `2 v < N`, hence `bitlen v < bitlen N`.
  The `96`-bit statement `bitlen v ≤ 95` is the special case; the mechanism is exact
  arithmetic at every scale.
* `firstDecile_fullsize_filter_eq_empty` — set-level form of "fraction removed = 1":
  the `v ≥ 2⁹⁵` filter deletes *every* first-decile point of a `96`-bit modulus.
* `midRegime_not_universal` / `spike_is_not_one_object` — explicit `96`-bit witnesses
  showing that in the middle regime (`0.1 < u < 0.21`) the band of a residue is *not*
  determined by its normalised position: at `u = 0.15` one modulus gives a full-size
  residue and another a sub-`2⁹⁵` one.  So position and bit-length are genuinely two
  different stratifications of the window; a positional-shape model needs both.
-/

open SpikeOrigin

/-! ## Scale-free band drop -/



/-! ### The size hypotheses are load-bearing

Both scale-free statements above carry a lower bound on `N`, and neither can simply be
dropped: the constants `0.45` and `1/2` genuinely fail for small moduli.  (An exhaustive
scan shows `N = 36482` is the last modulus violating `100 v < 45 N`, and `N = 962` the last
one violating `2 v < N`, so the hypothesis `2¹⁶ ≤ N` is close to sharp for the first bound
and generous for the second.) -/



/-! ## Set-level degeneracy of the exclusion clause -/


/-! ## The middle regime is genuinely modulus-dependent -/

theorem SpikeOrigin.midRegime_fullsize_witness:
    ∃ N j : ℕ, 2 ^ 95 ≤ N ∧ N < 2 ^ 96 ∧ Nat.sqrt N < j ∧ j ≤ 3 * Nat.sqrt N ∧
      100 * (j - Nat.sqrt N) ≤ 15 * (2 * Nat.sqrt N) ∧ 2 ^ 95 ≤ resid N j := by sorry
