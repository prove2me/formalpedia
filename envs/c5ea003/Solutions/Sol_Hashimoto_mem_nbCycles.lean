-- Prove2me | solution 1 for Hashimoto.mem_nbCycles
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:41:23.134829+00:00
-- url     : https://prove2.me/submissions/8044774b-7187-4caa-980e-a96af4c297b2

-- Sol generated from Algebra/NonBacktracking/HashimotoTrace.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount
import Theorems.Thm_Hashimoto_mem_closedNBWalks

/-!
# `trace (Bⁿ)` counts rooted closed non-backtracking walks of length `n`

Let `G` be a finite simple graph and let `B` be its **Hashimoto (non-backtracking)
matrix**: the `0-1` matrix indexed by the *darts* (oriented edges) of `G` with

`B d d' = 1` iff `d` and `d'` are composable (`d.snd = d'.fst`) and `d'` is not the
reversal of `d`.

The main results of this file are the two forms of the trace formula:

* `Hashimoto.trace_hashimoto_pow` :
  `trace (B ^ n) = #{ rooted closed non-backtracking walks of length n }`,
  where such a walk is a list of `n + 1` darts, consecutive darts composable without
  backtracking, whose first and last dart agree (the root);
* `Hashimoto.trace_hashimoto_pow_eq_card_nbCycles` (for `1 ≤ n`) :
  `trace (B ^ n) = #{ cyclically non-backtracking sequences of n darts }`,
  the classical "rooted closed non-backtracking walk of length `n`" of Ihara-zeta
  theory: `n` darts arranged in a cycle, non-backtracking also across the seam.

Both counts are genuine finite cardinalities (`Finset.card`), and the two counting
sets are proved to be in bijection (`Hashimoto.card_nbCycles`).

We also prove the first structural consequences:

* `Hashimoto.trace_hashimoto_pow_zero` : `trace (B ^ 0) = #darts = ∑ v, deg v`;
* `Hashimoto.trace_hashimoto` and `Hashimoto.trace_hashimoto_sq` : `trace B = trace (B²) = 0`
  (a graph has no closed non-backtracking walks of length `1` or `2`);
* `Hashimoto.rowSum_hashimoto` : the `d`-th row of `B` sums to `deg (d.snd) - 1`;
* `Hashimoto.trace_hashimoto_pow_le_of_regular` : for a `(q+1)`-regular graph,
  `trace (B ^ n) ≤ (#darts) * qⁿ`, i.e. the exponential growth rate of the number of
  closed non-backtracking walks is at most `q` (the Ihara/Alon–Boppana regime).

The underlying general digraph walk-counting machinery lives in
`Algebra.NonBacktracking.RelWalkCount`.
-/

open Finset RelWalkCount SimpleGraph

open Hashimoto

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


/-! ## The non-backtracking relation on darts -/



variable {G}




variable (G)

/-! ## The Hashimoto matrix -/



/-! ## Rooted closed non-backtracking walks -/





/-! ## The cyclic description -/


variable {G}

/-- `getLast?` ignores a prepended element as long as the tail is nonempty. -/
private lemma head?_dropLast {α : Type*} {l : List α} (h : 2 ≤ l.length) :
    l.dropLast.head? = l.head? := by
  match l, h with
  | x :: y :: t, _ => simp [List.dropLast]

/-- A closed walk is its own truncation with the root appended again. -/
private lemma eq_dropLast_append {α : Type*} {l : List α} (hne : l ≠ []) {x : α}
    (hx : l.head? = some x) (hend : l.head? = l.getLast?) : l = l.dropLast ++ [x] := by
  have hg : l.getLast? = some (l.getLast hne) := List.getLast?_eq_some_getLast hne
  have hsome : some (l.getLast hne) = some x := by rw [← hg, ← hend, hx]
  have hgx : l.getLast hne = x := by simpa using hsome
  conv_lhs => rw [← List.dropLast_append_getLast hne, hgx]



variable (G)


/-! ## First consequences -/






/-! ## Length three: closed non-backtracking walks are oriented triangles -/


variable {G}



variable (G)


/-! ## Row sums and the Ihara growth bound -/





open Hashimoto in
theorem solution{n : ℕ} (hn : 1 ≤ n) {c : List G.Dart} :
    c ∈ nbCycles G n ↔
      c.length = n ∧ List.IsChain (NBAdj G) c ∧
        ∀ x ∈ c.getLast?, ∀ y ∈ c.head?, NBAdj G x y := by
  constructor
  · rintro hc
    simp only [nbCycles, Finset.mem_image] at hc
    obtain ⟨l, hl, rfl⟩ := hc
    rw [mem_closedNBWalks] at hl
    obtain ⟨hlen, hchain, hend⟩ := hl
    have h2 : 2 ≤ l.length := by omega
    have hne : l ≠ [] := by intro h; rw [h] at hlen; simp at hlen
    obtain ⟨x, hx⟩ : ∃ x, l.head? = some x := by
      cases l with
      | nil => exact absurd rfl hne
      | cons a t => exact ⟨a, rfl⟩
    have hrep : l = l.dropLast ++ [x] := eq_dropLast_append hne hx hend
    have hchain' := hchain
    rw [hrep, List.isChain_append] at hchain'
    refine ⟨by simp [List.length_dropLast, hlen], hchain'.1, ?_⟩
    intro z hz y hy
    rw [head?_dropLast h2, hx] at hy
    have hxy : x = y := by simpa using hy
    have hfin := hchain'.2.2 z hz x (by simp)
    rwa [hxy] at hfin
  · rintro ⟨hlen, hchain, hseam⟩
    have hne : c ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen; omega
    obtain ⟨x, hx⟩ : ∃ x, c.head? = some x := by
      cases c with
      | nil => exact absurd rfl hne
      | cons a t => exact ⟨a, rfl⟩
    simp only [nbCycles, Finset.mem_image]
    refine ⟨c ++ [x], ?_, by simp⟩
    rw [mem_closedNBWalks]
    refine ⟨by simp [hlen], ?_, ?_⟩
    · rw [List.isChain_append]
      refine ⟨hchain, List.isChain_singleton _, ?_⟩
      intro z hz y hy
      have hxy : x = y := by simpa using hy
      rw [← hxy]
      exact hseam z hz x hx
    · have h1 : (c ++ [x]).head? = some x := by
        cases c with
        | nil => exact absurd rfl hne
        | cons a t => simpa using hx
      rw [h1]
      simp
