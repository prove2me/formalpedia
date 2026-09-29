-- Prove2me | solution 1 for SpikeOrigin.midRegime_tiny_witness
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:12:06.807857+00:00
-- url     : https://prove2.me/submissions/336aed7f-1da2-4d63-9b2b-61a6919653a3

-- Sol generated from Cryptography/SpikeOriginBands.lean
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






open SpikeOrigin in
theorem solution:
    ∃ N j : ℕ, 2 ^ 95 ≤ N ∧ N < 2 ^ 96 ∧ Nat.sqrt N < j ∧ j ≤ 3 * Nat.sqrt N ∧
      15 * (2 * Nat.sqrt N) ≤ 100 * (j - Nat.sqrt N) ∧ resid N j < 2 ^ 95 := by
  refine ⟨199032864766431 * 199032864766431, 278646010673003, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · rw [Nat.sqrt_eq]; norm_num
  · rw [Nat.sqrt_eq]; norm_num
  · rw [Nat.sqrt_eq]; norm_num
  · rw [resid]
    have e : (278646010673003 : ℕ) ^ 2 = 77643599263979301788993038009 := by norm_num
    have f : (2 : ℕ) ^ 95 = 39614081257132168796771975168 := by norm_num
    have g : (199032864766431 : ℕ) * 199032864766431 =
        39614081257132410564184477761 := by norm_num
    omega
