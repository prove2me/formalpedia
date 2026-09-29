-- Prove2me | solution 1 for AdjSum.cycExt_surjective_on_periodic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:21:07.410423+00:00
-- url     : https://prove2.me/submissions/832c01bb-8cec-4af0-abaa-79a77b1531fa

-- Sol generated from Applications/AdjacentSumPolytopes/GaussCongruence.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_GaussCongruence
import Definitions.Def_Applications_AdjacentSumPolytopes_Necklace
import Theorems.Thm_AdjSum_period_mod

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


@[simp] lemma idx_val (e m : ℕ) : (idx e m).val = m % (e + 1) := rfl

lemma idx_self (e : ℕ) (i : Fin (e + 1)) : idx e i.val = i :=
  Fin.ext (by simp [idx, Nat.mod_eq_of_lt i.isLt])



/-! ## Iterates of the rotation -/





/-! ## Periodic extension of cyclic words -/








/-! ## Exact-period counts -/





/-! ## The necklace decomposition of the trace sequence -/










open AdjSum in
theorem solution{s e q : ℕ} (h : (e + 1) ∣ (q + 1)) (x : CycPt s q)
    (hx : (rot s q)^[e + 1] x = x) : ∃ y : CycPt s e, cycExt h y = x := by
  have hle : e + 1 ≤ q + 1 := Nat.le_of_dvd (Nat.succ_pos q) h
  have hmem : (fun j : Fin (e + 1) => x.1 (idx q j.val)) ∈ cycSet s e := by
    rw [mem_cycSet]
    intro j
    have hj : j.val < q + 1 := lt_of_lt_of_le j.isLt hle
    have hx1 := (mem_cycSet.mp x.2) (idx q j.val)
    have hstep : (idx q j.val) + 1 = idx q (j.val + 1) := idx_add_one q j.val
    rw [hstep] at hx1
    have h2 : x.1 (idx q (j.val + 1)) = x.1 (idx q ((j + 1).val)) := by
      rw [period_mod x hx (j.val + 1)]
      refine congrArg _ (congrArg _ ?_)
      show (j.val + 1) % (e + 1) = (j.val + (1 : Fin (e + 1)).val) % (e + 1)
      rw [Fin.val_one', add_one_mod_dvd dvd_rfl]
    rw [h2] at hx1
    exact hx1
  refine ⟨⟨_, hmem⟩, ?_⟩
  refine Subtype.ext ?_
  funext i
  show x.1 (idx q ((idx e i.val).val)) = x.1 i
  rw [idx_val, ← period_mod x hx i.val, idx_self]
