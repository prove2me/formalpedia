-- Prove2me | Definitions.Def_Shared_ZeroKnowledge_PCPBridge
-- name    : Shared_ZeroKnowledge_PCPBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:16:16.192815+00:00
-- url     : https://prove2.me/theorems/1905308e-fed8-458d-8153-5329c8efc0d3
-- title:
--   Aether Catalog definitions — Shared_ZeroKnowledge_PCPBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ZeroKnowledge.PCPBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ZeroKnowledge/PCPBridge.lean by skeleton subtraction
import Mathlib

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

namespace ZKPCPBridge

variable {V : Type*}

/-! ## The two-query verifier -/

/-- `c` is a proper 3-colouring of the edge list `E`. -/
def IsProper (E : Finset (V × V)) (c : V → Fin 3) : Prop := ∀ e ∈ E, c e.1 ≠ c e.2

/-- The instance is a yes-instance of 3-colorability. -/
def ThreeColorable (E : Finset (V × V)) : Prop := ∃ c : V → Fin 3, IsProper E c

/-- The verdict of the verifier on the test `e` given the proof string `f`. -/
def Accepts (f : V → Fin 3) (e : V × V) : Prop := f e.1 ≠ f e.2

instance (f : V → Fin 3) (e : V × V) : Decidable (Accepts f e) := by
  unfold Accepts; infer_instance

/-- The proof positions queried by the test `e`. -/
def queries [DecidableEq V] (e : V × V) : Finset V := {e.1, e.2}



/-- The number of tests the verifier accepts. -/
def accCard (E : Finset (V × V)) (f : V → Fin 3) : ℕ := (E.filter (Accepts f)).card

/-- The acceptance probability of the verifier, over a uniformly random test. -/
noncomputable def accProb (E : Finset (V × V)) (f : V → Fin 3) : ℝ :=
  (accCard E f : ℝ) / E.card







/-! ## Exact parallel repetition -/

/-- The test space of the `k`-fold parallel repetition: `k` independent edges. -/
def prodTests [DecidableEq V] (E : Finset (V × V)) (k : ℕ) : Finset (Fin k → V × V) :=
  Fintype.piFinset fun _ => E

/-- The `k`-fold repeated verifier accepts iff all `k` tests accept. -/
def ProdAccepts (k : ℕ) (f : V → Fin 3) (v : Fin k → V × V) : Prop := ∀ i, Accepts f (v i)

instance (k : ℕ) (f : V → Fin 3) (v : Fin k → V × V) : Decidable (ProdAccepts k f v) := by
  unfold ProdAccepts; infer_instance








end ZKPCPBridge


