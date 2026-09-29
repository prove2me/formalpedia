-- Prove2me | solution 1 for Catalog.Probability.SeedRec.lfsr_seq_determined_by_two_L
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:22:39.609565+00:00
-- url     : https://prove2.me/submissions/02d98045-e67a-4beb-b895-4edcd941195f

-- Sol generated from Probability/PRNGBerlekampMassey.lean
import Mathlib
import Definitions.Def_Probability_PRNGBerlekampMassey
import Definitions.Def_Probability_PRNGLFSRDetection
import Theorems.Thm_Catalog_Probability_SeedRec_eq_zero_of_annihilated
import Theorems.Thm_Catalog_Probability_SeedRec_satisfiesLFSR_iff_aeval

/-!
# How many symbols certify a recovered seed?  The `2L` theorem

Berlekamp–Massey recovers a length-`L` LFSR from an observed window.  The
practical question for a seed-compressor is: **after how many observed symbols
is the recovered generator guaranteed to reproduce the rest of the file?**  This
file answers it: `2L` symbols suffice, for the whole family at once.

The proof runs through the module structure of `ℕ → K` over the polynomial ring,
with `X` acting as the shift operator:

* `shiftEnd` — the shift as a `K`-linear endomorphism of `ℕ → K`;
* `aeval_shiftEnd_apply` — the action of a polynomial is the associated linear
  recurrence operator;
* `charPolyLFSR`, `satisfiesLFSR_iff_aeval` — a stream is an order-`L` LFSR
  stream (taps `c`) exactly when its characteristic polynomial annihilates it;
* `eq_zero_of_annihilated` — a sequence annihilated by a monic polynomial of
  degree `m` and vanishing on `[0, m)` vanishes identically (rigidity);
* `aeval_mul_sub_eq_zero` — the difference of two sequences with annihilators
  `f` and `g` is annihilated by `f * g` (this is where the two *different* tap
  vectors get merged);
* `lfsr_seq_determined_by_two_L` — **the `2L` theorem**: two sequences each of
  linear complexity `≤ L` that agree on the first `2L` symbols agree forever;
* `lfsr_stream_determined_by_two_L` — the same statement for the concrete
  generators: matching `2L` output symbols certifies the recovered seed *and*
  taps for the entire, arbitrarily long, file.

The computational counterpart is the saturation observed in
`ComputationalEvidence.md`: over `GF(2)` the number of length-`n` words of
linear complexity `≤ L` is strictly increasing in `n` until `n = 2L`, and
constant afterwards.
-/

open Catalog.Probability.SeedRec

open Polynomial

variable {K : Type*} [CommRing K]




variable {L : ℕ}


theorem degree_taps_lt (c : Fin L → K) :
    (∑ j : Fin L, C (c j) * X ^ (j : ℕ) : K[X]).degree < (L : ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe L)]
  intro j _
  exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) (by exact_mod_cast j.isLt)

theorem charPolyLFSR_monic (c : Fin L → K) : (charPolyLFSR c).Monic :=
  Polynomial.monic_X_pow_sub (degree_taps_lt c)

theorem charPolyLFSR_natDegree [Nontrivial K] (c : Fin L → K) :
    (charPolyLFSR c).natDegree = L := by
  have h2 := Polynomial.degree_sub_eq_left_of_degree_lt
    (p := (X ^ L : K[X])) (q := ∑ j : Fin L, C (c j) * X ^ (j : ℕ))
    (by simpa using degree_taps_lt c)
  simpa [charPolyLFSR] using Polynomial.natDegree_eq_of_degree_eq h2



/-- Annihilators multiply: the difference of a sequence annihilated by `f` and a
sequence annihilated by `g` is annihilated by `f * g`. -/
theorem aeval_mul_sub_eq_zero {f g : K[X]} {y z : ℕ → K}
    (hy : aeval (shiftEnd K) f y = 0) (hz : aeval (shiftEnd K) g z = 0) :
    aeval (shiftEnd K) (f * g) (y - z) = 0 := by
  have hy' : aeval (shiftEnd K) (f * g) y = 0 := by
    rw [mul_comm, map_mul]
    show (aeval (shiftEnd K) g) ((aeval (shiftEnd K) f) y) = 0
    rw [hy, map_zero]
  have hz' : aeval (shiftEnd K) (f * g) z = 0 := by
    rw [map_mul]
    show (aeval (shiftEnd K) f) ((aeval (shiftEnd K) g) z) = 0
    rw [hz, map_zero]
  rw [map_sub, hy', hz', sub_zero]




open Catalog.Probability.SeedRec in
theorem solution[Nontrivial K] (c c' : Fin L → K) (y z : ℕ → K)
    (hy : SatisfiesLFSR c y) (hz : SatisfiesLFSR c' z)
    (hagree : ∀ t < 2 * L, y t = z t) : y = z := by
  have hy' := (satisfiesLFSR_iff_aeval c y).1 hy
  have hz' := (satisfiesLFSR_iff_aeval c' z).1 hz
  have hprod : aeval (shiftEnd K) (charPolyLFSR c * charPolyLFSR c') (y - z) = 0 :=
    aeval_mul_sub_eq_zero hy' hz'
  have hmonic : (charPolyLFSR c * charPolyLFSR c').Monic :=
    (charPolyLFSR_monic c).mul (charPolyLFSR_monic c')
  have hdeg : (charPolyLFSR c * charPolyLFSR c').natDegree = 2 * L := by
    rw [(charPolyLFSR_monic c).natDegree_mul (charPolyLFSR_monic c'),
      charPolyLFSR_natDegree, charPolyLFSR_natDegree]
    ring
  have hvan : ∀ t < (charPolyLFSR c * charPolyLFSR c').natDegree, (y - z) t = 0 := by
    intro t ht
    rw [hdeg] at ht
    simp [hagree t ht]
  have := eq_zero_of_annihilated _ hmonic _ hprod hvan
  funext t
  have := congrFun this t
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this
