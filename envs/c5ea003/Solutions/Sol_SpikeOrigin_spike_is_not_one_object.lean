-- Prove2me | solution 1 for SpikeOrigin.spike_is_not_one_object
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:13:45.923218+00:00
-- url     : https://prove2.me/submissions/cca7e263-ed04-4440-95c2-83785cd471b7

-- Sol generated from Cryptography/SpikeOriginBands.lean
import Mathlib
import Definitions.Def_Cryptography_SpikeOriginDegeneracy
import Theorems.Thm_SpikeOrigin_firstDecile_bitlen_le_95
import Theorems.Thm_SpikeOrigin_midRegime_fullsize_witness
import Theorems.Thm_SpikeOrigin_midRegime_tiny_witness
import Theorems.Thm_SpikeOrigin_resid_ge_two_pow_95_of_far
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
    (∀ N j : ℕ, 2 ^ 95 ≤ N → N < 2 ^ 96 → FirstDecile N j → (resid N j).size ≤ 95) ∧
    (∀ N j : ℕ, 2 ^ 95 ≤ N → N < 2 ^ 96 → 142 * Nat.sqrt N ≤ 100 * j →
      96 ≤ (resid N j).size) ∧
    (∃ N j : ℕ, 2 ^ 95 ≤ N ∧ N < 2 ^ 96 ∧ 100 * (j - Nat.sqrt N) ≤ 15 * (2 * Nat.sqrt N) ∧
      96 ≤ (resid N j).size) ∧
    (∃ N j : ℕ, 2 ^ 95 ≤ N ∧ N < 2 ^ 96 ∧ 15 * (2 * Nat.sqrt N) ≤ 100 * (j - Nat.sqrt N) ∧
      (resid N j).size ≤ 95) := by
  refine ⟨fun N j hlo hhi h => firstDecile_bitlen_le_95 hlo hhi h, ?_, ?_, ?_⟩
  · intro N j hlo hhi hfar
    have h := resid_ge_two_pow_95_of_far hlo hhi hfar
    by_contra hcon
    push_neg at hcon
    have := Nat.size_le.1 (Nat.le_of_lt_succ (by omega : (resid N j).size < 96))
    omega
  · obtain ⟨N, j, h1, h2, _, _, h5, h6⟩ := midRegime_fullsize_witness
    refine ⟨N, j, h1, h2, h5, ?_⟩
    by_contra hcon
    push_neg at hcon
    have := Nat.size_le.1 (Nat.le_of_lt_succ (by omega : (resid N j).size < 96))
    omega
  · obtain ⟨N, j, h1, h2, _, _, h5, h6⟩ := midRegime_tiny_witness
    exact ⟨N, j, h1, h2, h5, Nat.size_le.2 h6⟩
