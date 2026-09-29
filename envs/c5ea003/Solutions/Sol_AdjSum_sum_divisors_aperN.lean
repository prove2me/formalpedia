-- Prove2me | solution 1 for AdjSum.sum_divisors_aperN
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:13:30.127965+00:00
-- url     : https://prove2.me/submissions/6e9a6ac4-7fb6-4c02-a4d7-f3604f57b21e

-- Sol generated from Applications/AdjacentSumPolytopes/GaussCongruence.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_GaussCongruence
import Definitions.Def_Applications_AdjacentSumPolytopes_Necklace
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence
import Theorems.Thm_AdjSum_card_minimalPeriod_eq_aper
import Theorems.Thm_AdjSum_cycCount_eq

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



lemma idx_self (e : ℕ) (i : Fin (e + 1)) : idx e i.val = i :=
  Fin.ext (by simp [idx, Nat.mod_eq_of_lt i.isLt])

theorem card_eq_sum_divisors_card_minimalPeriod {α : Type*} [Fintype α] [DecidableEq α]
    {f : α → α} {N : ℕ} (hN : 0 < N) (hfN : ∀ x, f^[N] x = x) :
    Fintype.card α
      = ∑ d ∈ N.divisors, (Finset.univ.filter
          (fun x : α => Function.minimalPeriod f x = d)).card := by
  classical
  have hmem : ∀ x : α, Function.minimalPeriod f x ∈ N.divisors := by
    intro x
    have hper : Function.IsPeriodicPt f N x := hfN x
    exact Nat.mem_divisors.mpr ⟨Function.IsPeriodicPt.minimalPeriod_dvd hper, hN.ne'⟩
  calc Fintype.card α = ∑ x : α, 1 := by
        simp
    _ = ∑ x : α, ∑ d ∈ N.divisors, (if Function.minimalPeriod f x = d then 1 else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [Finset.sum_ite_eq, hmem x]
    _ = ∑ d ∈ N.divisors, ∑ x : α, (if Function.minimalPeriod f x = d then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ N.divisors,
        (Finset.univ.filter (fun x : α => Function.minimalPeriod f x = d)).card := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.card_filter]



/-! ## Iterates of the rotation -/

lemma rot_iterate_apply (s q k : ℕ) (x : CycPt s q) (i : Fin (q + 1)) :
    ((rot s q)^[k] x).1 i = x.1 (idx q (i.val + k)) := by
  induction k generalizing x i with
  | zero => simp [idx_self]
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      rw [ih (rot s q x) i]
      show x.1 ((idx q (i.val + k)) + 1) = _
      rw [idx_add_one, Nat.add_assoc]

lemma rot_iterate_card (s q : ℕ) (x : CycPt s q) : (rot s q)^[q + 1] x = x := by
  refine Subtype.ext ?_
  funext i
  rw [rot_iterate_apply]
  refine congrArg _ (Fin.ext ?_)
  simp [idx, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]



/-! ## Periodic extension of cyclic words -/








/-! ## Exact-period counts -/





/-! ## The necklace decomposition of the trace sequence -/


lemma aperN_succ (s q : ℕ) : aperN s (q + 1) = aperCyc s q := by simp [aperN]








open AdjSum in
theorem solution(s n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, (aperN s d : ℤ) = traceSeq s n := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  have hcard : Fintype.card (CycPt s q) = cycCount s q := by
    rw [cycCount]; exact Fintype.card_coe _
  have hsplit := card_eq_sum_divisors_card_minimalPeriod (f := rot s q)
    (Nat.succ_pos q) (rot_iterate_card s q)
  rw [hcard] at hsplit
  have hterm : ∀ d ∈ (q + 1).divisors,
      (Finset.univ.filter
        (fun x : CycPt s q => Function.minimalPeriod (rot s q) x = d)).card = aperN s d := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by
      rcases Nat.eq_zero_or_pos d with rfl | hd0
      · exact absurd (Nat.eq_zero_of_zero_dvd hd.1) (by omega)
      · omega⟩
    rw [aperN_succ]
    exact card_minimalPeriod_eq_aper hd.1
  rw [Finset.sum_congr rfl hterm] at hsplit
  have : (cycCount s q : ℤ) = ∑ d ∈ (q + 1).divisors, (aperN s d : ℤ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) hsplit
  rw [← this, cycCount_eq, traceSeq]
