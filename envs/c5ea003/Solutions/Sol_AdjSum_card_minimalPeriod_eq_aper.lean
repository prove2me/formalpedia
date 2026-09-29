-- Prove2me | solution 1 for AdjSum.card_minimalPeriod_eq_aper
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:11:34.078624+00:00
-- url     : https://prove2.me/submissions/49531a00-e38f-4273-af78-13938a4f9a90

-- Sol generated from Applications/AdjacentSumPolytopes/GaussCongruence.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_GaussCongruence
import Definitions.Def_Applications_AdjacentSumPolytopes_Necklace
import Theorems.Thm_AdjSum_cycExt_surjective_on_periodic
import Theorems.Thm_AdjSum_minimalPeriod_cycExt

/-!
# The full Gauss congruence for the adjacent-sum transfer matrix

`Applications.AdjacentSumPolytopes.Necklace` proved the Gauss congruence
`p ∣ tr(Mᵖ) − tr(M)` for *prime* lengths, using the `p`-group fixed point formula, and
left the general case as a conjecture.  Here we settle it:

`n ∣ ∑_{d ∣ n} μ(n/d) · tr(Mⁿ)`   for every `n ≥ 1`,

where `M = adjMat s` is the adjacent-sum transfer matrix.  Equivalently the *primitive*
cyclic counts `primCyc s n` — the Möbius transform of the trace sequence — count the
aperiodic cyclic adjacent-sum words, hence are divisible by their length.

The proof is the necklace argument, made precise:

* `cycExt` extends a cyclic word of length `e + 1` periodically to a cyclic word of
  length `q + 1` whenever `(e+1) ∣ (q+1)`; it is injective, rotation-equivariant, and its
  image is exactly the set of `(e+1)`-periodic words (`cycExt_surjective_on_periodic`);
* therefore the number of length-`(q+1)` words of *exact* period `d` equals the number of
  *aperiodic* words of length `d` (`card_minimalPeriod_eq_aper`);
* the abstract orbit-peeling lemma of `Applications.AdjacentSumPolytopes.Periodicity`
  gives `d ∣ aperCyc s d`, and Möbius inversion identifies `aperCyc s n = primCyc s n`.

-- !-- Lab Notes -- !--
* **Hypothesis.** `primCyc s n` counts aperiodic cyclic adjacent-sum words of length `n`,
  hence `n ∣ primCyc s n` for all `n ≥ 1`, not only for `n` prime.
* **Experiment.** `s = 2`, trace sequence `tr(Mⁿ) = 2, 6, 11, 26, 57, 129, 289` for
  `n = 1..7`.  Möbius transforms: `primCyc 1 = 2`, `primCyc 2 = 6 - 2 = 4`,
  `primCyc 3 = 11 - 2 = 9`, `primCyc 4 = 26 - 6 = 20`, `primCyc 6 = 129 - 11 - 6 + 2 = 114`.
  Divisibility: `1∣2`, `2∣4`, `3∣9`, `4∣20`, `6∣114 = 6·19`.  The composite cases `4` and
  `6` are exactly the ones the prime-only argument could not reach.
* **Analysis.** The obstruction in the previous cycle was that the `p`-group fixed-point
  theorem only sees prime lengths.  Replacing it by the exact-period decomposition
  removes the arithmetic hypothesis entirely: the only input is that rotation is an
  injective map with `rot^[n] = id`.
* **Critique.** The argument nowhere assumes the alphabet nonempty or the constraint
  nontrivial; the degenerate readings are still true statements, and for `s ≥ 0` the
  counts are positive (the all-zero word is always admissible), so the congruence is not
  vacuous.
-/

open AdjSum

open Finset Function Matrix






/-! ## Iterates of the rotation -/





/-! ## Periodic extension of cyclic words -/




lemma cycExt_apply {s e q : ℕ} (h : (e + 1) ∣ (q + 1)) (y : CycPt s e) (i : Fin (q + 1)) :
    (cycExt h y).val i = y.val (idx e i.val) := rfl

lemma cycExt_injective {s e q : ℕ} (h : (e + 1) ∣ (q + 1)) :
    Function.Injective (cycExt (s := s) h) := by
  intro y z hyz
  have hle : e + 1 ≤ q + 1 := Nat.le_of_dvd (Nat.succ_pos q) h
  refine Subtype.ext ?_
  funext j
  have hj : j.val < q + 1 := lt_of_lt_of_le j.isLt hle
  have := congrArg (fun w : CycPt s q => w.1 ⟨j.val, hj⟩) hyz
  simpa [cycExt_apply, idx, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt j.isLt] using this




/-! ## Exact-period counts -/





/-! ## The necklace decomposition of the trace sequence -/










open AdjSum in
theorem solution{s e q : ℕ} (h : (e + 1) ∣ (q + 1)) :
    (Finset.univ.filter
      (fun x : CycPt s q => Function.minimalPeriod (rot s q) x = e + 1)).card
      = aperCyc s e := by
  rw [aperCyc]
  refine (Finset.card_bij (fun y _ => cycExt h y) ?_ ?_ ?_).symm
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨Finset.mem_univ _, by rw [minimalPeriod_cycExt]; exact hy.2⟩
  · intro y _ z _ hyz
    exact cycExt_injective h hyz
  · intro x hx
    rw [Finset.mem_filter] at hx
    have hper : (rot s q)^[e + 1] x = x :=
      Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr (by rw [hx.2])
    obtain ⟨y, hy⟩ := cycExt_surjective_on_periodic h x hper
    refine ⟨y, ?_, hy⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← minimalPeriod_cycExt h y, hy]
    exact hx.2
