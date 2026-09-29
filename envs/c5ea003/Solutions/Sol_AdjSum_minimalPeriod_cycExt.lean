-- Prove2me | solution 1 for AdjSum.minimalPeriod_cycExt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:10:05.550769+00:00
-- url     : https://prove2.me/submissions/80ccd1b6-529c-4c99-adfd-b2d9d907d45e

-- Sol generated from Applications/AdjacentSumPolytopes/GaussCongruence.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_GaussCongruence
import Definitions.Def_Applications_AdjacentSumPolytopes_Necklace

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

lemma cycExt_rot {s e q : ℕ} (h : (e + 1) ∣ (q + 1)) (y : CycPt s e) :
    cycExt h (rot s e y) = rot s q (cycExt h y) := by
  refine Subtype.ext ?_
  funext i
  show (rot s e y).1 (idx e i.val) = (cycExt h y).1 (i + 1)
  show y.1 (idx e i.val + 1) = y.1 (idx e ((i + 1).val))
  refine congrArg _ (Fin.ext ?_)
  rw [idx_add_one]
  show (i.val + 1) % (e + 1) = ((i.val + (1 : Fin (q + 1)).val) % (q + 1)) % (e + 1)
  rw [Fin.val_one', Nat.mod_mod_of_dvd _ h, add_one_mod_dvd h]

lemma cycExt_iterate {s e q : ℕ} (h : (e + 1) ∣ (q + 1)) (y : CycPt s e) (k : ℕ) :
    cycExt h ((rot s e)^[k] y) = (rot s q)^[k] (cycExt h y) := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, cycExt_rot]


/-! ## Exact-period counts -/





/-! ## The necklace decomposition of the trace sequence -/










open AdjSum in
theorem solution{s e q : ℕ} (h : (e + 1) ∣ (q + 1)) (y : CycPt s e) :
    Function.minimalPeriod (rot s q) (cycExt h y) = Function.minimalPeriod (rot s e) y := by
  have key : ∀ k : ℕ, Function.IsPeriodicPt (rot s q) k (cycExt h y)
      ↔ Function.IsPeriodicPt (rot s e) k y := by
    intro k
    constructor
    · intro hk
      have : cycExt h ((rot s e)^[k] y) = cycExt h y := by
        rw [cycExt_iterate]; exact hk
      exact cycExt_injective h this
    · intro hk
      show (rot s q)^[k] (cycExt h y) = cycExt h y
      rw [← cycExt_iterate]
      exact congrArg _ hk
  refine Nat.dvd_antisymm ?_ ?_
  · exact Function.isPeriodicPt_iff_minimalPeriod_dvd.mp
      ((key _).mpr (Function.isPeriodicPt_minimalPeriod _ _))
  · exact Function.isPeriodicPt_iff_minimalPeriod_dvd.mp
      ((key _).mp (Function.isPeriodicPt_minimalPeriod _ _))
