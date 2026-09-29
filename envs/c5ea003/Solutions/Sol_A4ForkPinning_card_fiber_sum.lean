-- Prove2me | solution 1 for A4ForkPinning.card_fiber_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:05:15.018187+00:00
-- url     : https://prove2.me/submissions/f07a98b6-9877-4e90-b655-1b2a98b7840c

-- Sol generated from Algebra/A4ForkPinning/MultiFactor.lean
import Mathlib
import Definitions.Def_Algebra_A4ForkPinning_Information
import Definitions.Def_Algebra_A4ForkPinning_MultiFactor
import Definitions.Def_Algebra_A4ForkPinning_Semiprime
/-
# The order-3 channel for `k` factors, and its collapse

The semiprime laws of `Semiprime.lean` are the case `k = 2` of a family.  Let
`N = p₁⋯p_{k+1}` be a product of `k+1` unramified primes of the `A₄`-field; the
dial `N mod 9` sees only the sum `s = Σ chi9(pᵢ) ∈ ℤ/3` of the cube classes.

* `A4ForkPinning.card_fiber_sum` — every fibre of the sum map
  `(ℤ/3)^{k+1} → ℤ/3` has exactly `3^k` points (proved by an explicit bijection);
* `A4ForkPinning.allSplitRate_eq_count` — hence `P(all factors split | s) = 3^{-k}`
  if `s = 0` and `0` otherwise: the "all split" fork is the `3^{-k}`-thinning of
  the pinned fork `[s = 0]`;
* `A4ForkPinning.info_all_split` — **the `k`-factor AND law**
  `I = H(3^{-(k+1)}) - (1/3)·H(3^{-k})`, generalising the semiprime value
  `H(1/9) - (1/3)H(1/3)`;
* `A4ForkPinning.info_all_split_strict` — it is a genuine leak: `0 < I < H(F)`;
* `A4ForkPinning.info_all_split_tendsto_zero` — **the channel collapses**:
  `I → 0` as the number of factors grows.  Quantitatively, the residue of a
  many-factor number tells one essentially nothing about its factors' splitting
  behaviour: the "factor-uselessness" of the pinned fork.
-/

open A4ForkPinning

open Finset

/-! ## Fibres of the sum map on `(ℤ/3)^{k+1}` -/



/-! ## The `k`-factor AND channel -/







/-! ## Collapse of the channel -/





open A4ForkPinning in
theorem solution(k : ℕ) (t : ZMod 3) :
    (univ.filter (fun x : Fin (k + 1) → ZMod 3 => ∑ i, x i = t)).card = 3 ^ k := by
  classical
  have h : (univ.filter (fun x : Fin (k + 1) → ZMod 3 => ∑ i, x i = t)).card
      = (univ : Finset (Fin k → ZMod 3)).card := by
    refine Finset.card_bij' (fun x _ => fun i => x i.castSucc)
      (fun y _ => Fin.snoc y (t - ∑ i, y i)) ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · intro b _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Fin.sum_univ_castSucc]
      simp [Fin.snoc]
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]
        rw [Fin.sum_univ_castSucc] at ha
        rw [← ha]; ring
      · intro j; simp [Fin.snoc_castSucc]
    · intro b _
      funext i
      simp [Fin.snoc]
  rw [h]
  simp
