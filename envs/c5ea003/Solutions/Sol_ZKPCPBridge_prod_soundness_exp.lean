-- Prove2me | solution 1 for ZKPCPBridge.prod_soundness_exp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:11:47.534764+00:00
-- url     : https://prove2.me/submissions/990271b8-ff88-4aca-983c-0ce2356721cd

-- Sol generated from Shared/ZeroKnowledge/PCPBridge.lean
import Mathlib
import Definitions.Def_Shared_ZeroKnowledge_PCPBridge
import Theorems.Thm_ZKPCPBridge_accProb_le_one_sub_inv

/-!
# Bridge to probabilistically checkable proofs: 3-colorability as a 2-query PCP

The zero-knowledge protocol for graph 3-colorability is, stripped of its commitments,
exactly a *probabilistically checkable proof*: the proof string is a colouring
`f : V → Fin 3`, the verifier tosses `log₂ |E|` coins to pick an edge and reads only the
**two** proof symbols at its endpoints. This file makes that verifier and its parameters
precise and proves the completeness/soundness gap together with an exact parallel
repetition theorem.

## Main results

* `card_queries_le_two` — the verifier reads at most two proof symbols per test.
* `accepts_of_agree_on_queries` — *locality*: the verdict depends only on the queried
  symbols, so the verifier really is a 2-query oracle machine.
* `accProb_eq_one_iff` — perfect completeness, and its exact converse.
* `accProb_le_one_sub_inv` — the PCP gap: non-3-colorable instances are accepted with
  probability at most `1 - 1/|E|`.
* `prodAccept_card` — **exact parallel repetition**: the number of accepting `k`-tuples of
  tests is the `k`-th power of the number of accepting tests, hence
  `prodAccProb_eq_pow : (accepting k-tuples)/(all k-tuples) = accProb ^ k`.
* `prod_queries_card_le` and `prod_soundness_exp` — `k` repetitions use at most `2k`
  queries and drive the soundness error down to `exp (-k/|E|)`; taking `k = |E| · t`
  gives error `exp (-t)` (`prod_soundness_scaled`). This is the query-complexity /
  soundness trade-off underlying the PCP view of this verifier.
-/

open Finset

open ZKPCPBridge

variable {V : Type*}

/-! ## The two-query verifier -/











theorem accProb_nonneg (E : Finset (V × V)) (f : V → Fin 3) : 0 ≤ accProb E f := by
  unfold accProb; positivity





/-! ## Exact parallel repetition -/












open ZKPCPBridge in
theorem solution[DecidableEq V] {E : Finset (V × V)} (hE : E.Nonempty)
    (h : ¬ ThreeColorable E) (f : V → Fin 3) (k : ℕ) :
    accProb E f ^ k ≤ Real.exp (-(k / E.card)) := by
  have hm : (0 : ℝ) < E.card := by exact_mod_cast card_pos.mpr hE
  have hle : (1 : ℝ) / E.card ≤ 1 := by
    rw [div_le_one hm]
    exact_mod_cast card_pos.mpr hE
  have hgap : accProb E f ≤ 1 - 1 / E.card := accProb_le_one_sub_inv hE h f
  have hnn : (0 : ℝ) ≤ accProb E f := accProb_nonneg E f
  have hstep : 1 - 1 / (E.card : ℝ) ≤ Real.exp (-(1 / E.card)) := by
    have := Real.add_one_le_exp (-(1 / (E.card : ℝ)))
    linarith
  have hchain : accProb E f ≤ Real.exp (-(1 / E.card)) := le_trans hgap hstep
  calc accProb E f ^ k ≤ (Real.exp (-(1 / E.card))) ^ k := by gcongr
    _ = Real.exp (-(k / E.card)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
