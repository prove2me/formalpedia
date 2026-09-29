-- Prove2me | solution 1 for Hashimoto.card_nbCycles
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:41:21.800459+00:00
-- url     : https://prove2.me/submissions/f748f2b4-4aff-443e-a484-f4e36a35bab7

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
theorem solution{n : ℕ} (hn : 1 ≤ n) :
    (nbCycles G n).card = (closedNBWalks G n).card := by
  refine Finset.card_image_of_injOn ?_
  intro l₁ h₁ l₂ h₂ hEq
  rw [Finset.mem_coe, mem_closedNBWalks] at h₁ h₂
  obtain ⟨hlen₁, -, hend₁⟩ := h₁
  obtain ⟨hlen₂, -, hend₂⟩ := h₂
  have hne₁ : l₁ ≠ [] := by intro h; rw [h] at hlen₁; simp at hlen₁
  have hne₂ : l₂ ≠ [] := by intro h; rw [h] at hlen₂; simp at hlen₂
  have h2₁ : 2 ≤ l₁.length := by omega
  have h2₂ : 2 ≤ l₂.length := by omega
  obtain ⟨x, hx⟩ : ∃ x, l₁.head? = some x := by
    cases l₁ with
    | nil => exact absurd rfl hne₁
    | cons a t => exact ⟨a, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, l₂.head? = some y := by
    cases l₂ with
    | nil => exact absurd rfl hne₂
    | cons a t => exact ⟨a, rfl⟩
  have hxy : x = y := by
    have e₁ : l₁.dropLast.head? = some x := by rw [head?_dropLast h2₁, hx]
    have e₂ : l₂.dropLast.head? = some y := by rw [head?_dropLast h2₂, hy]
    rw [hEq, e₂] at e₁
    simpa using e₁.symm
  subst hxy
  rw [eq_dropLast_append hne₁ hx hend₁, eq_dropLast_append hne₂ hy hend₂, hEq]
