-- Prove2me | solution 1 for ZKPCPBridge.accProb_le_one_sub_inv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:10:28.750396+00:00
-- url     : https://prove2.me/submissions/6e1ff7cf-66f4-47dd-98e8-7e2e29be7c6f

-- Sol generated from Shared/ZeroKnowledge/PCPBridge.lean
import Mathlib
import Definitions.Def_Shared_ZeroKnowledge_PCPBridge

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
















/-! ## Exact parallel repetition -/












open ZKPCPBridge in
theorem solution[DecidableEq V] {E : Finset (V × V)} (hE : E.Nonempty)
    (h : ¬ ThreeColorable E) (f : V → Fin 3) : accProb E f ≤ 1 - 1 / E.card := by
  have hbad : ∃ e ∈ E, ¬ Accepts f e := by
    by_contra hcon
    push_neg at hcon
    exact h ⟨f, fun e he => hcon e he⟩
  obtain ⟨e₀, he₀, hbad⟩ := hbad
  have hsub : E.filter (Accepts f) ⊆ E.erase e₀ := by
    intro e he
    rw [mem_filter] at he
    exact mem_erase.mpr ⟨by rintro rfl; exact hbad he.2, he.1⟩
  have hcard : accCard E f + 1 ≤ E.card := by
    have h1 : accCard E f ≤ (E.erase e₀).card := card_le_card hsub
    have h2 : (E.erase e₀).card = E.card - 1 := card_erase_of_mem he₀
    have h3 : 1 ≤ E.card := card_pos.mpr hE
    omega
  have hm : (0 : ℝ) < E.card := by exact_mod_cast card_pos.mpr hE
  have h1 : (accCard E f : ℝ) ≤ (E.card : ℝ) - 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at this
    linarith
  rw [accProb, div_le_iff₀ hm]
  have hmul : (1 - 1 / (E.card : ℝ)) * E.card = (E.card : ℝ) - 1 := by field_simp
  rw [hmul]
  exact h1
