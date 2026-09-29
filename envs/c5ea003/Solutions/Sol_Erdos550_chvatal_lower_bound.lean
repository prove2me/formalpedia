-- Prove2me | solution 1 for Erdos550.chvatal_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:07:07.726605+00:00
-- url     : https://prove2.me/submissions/f8220fe2-5cc1-4b1d-8e59-41099a6a5cb5

-- Sol generated from Novelty/ErdosProblem550Chvatal.lean
import Mathlib
import Definitions.Def_Novelty_ErdosProblem550Chvatal
import Theorems.Thm_Erdos550_no_blue_clique
import Theorems.Thm_Erdos550_no_red_connected
/-
# Erdős Problem 550 — the all-ones (Chvátal) case: lower bound

Erdős Problem 550 conjectures that for fixed `k ≥ 2` and `1 ≤ m₁ ≤ ⋯ ≤ m_k`,
for all sufficiently large `n` and every `n`-vertex tree `T`,
`R(T, K_{m₁,…,m_k}) ≤ (k-1)(R(T, K_{m₁,m₂}) - 1) + m₁`.

The **all-ones special case** `m₁ = ⋯ = m_k = 1` is especially clean: the complete
multipartite graph with every part of size one is the complete graph `K_k`, and
`R(T, K_{1,1}) = R(T, K₂) = n` (a single blue edge is avoided only by an all-red
colouring, i.e. a complete graph, which contains the `n`-vertex tree iff it has
`≥ n` vertices).  The conjectured bound then reads

  `R(T, K_k) ≤ (k-1)(n-1) + 1`,

which is exactly **Chvátal's theorem** `R(T_n, K_k) = (k-1)(n-1) + 1`.

This file proves the **lower bound** half of Chvátal's theorem, i.e. that the
Erdős–550 bound is *tight* for the all-ones case:

  `R(T, K_k) > (k-1)(n-1)`,

witnessed by the extremal colouring whose red graph is a disjoint union of
`k-1` red cliques each on `n-1` vertices.

* No red copy of `T`: each red component has only `n-1 < n` vertices, while the
  tree `T` is connected on `n` vertices, so cannot be embedded.
* No blue copy of `K_k`: the blue graph is complete `(k-1)`-partite, so its
  cliques are transversals of at most `k-1` parts.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The Erdős–550 bound is tight; in the all-ones case the
  disjoint-clique colouring should witness `R(T,K_k) > (k-1)(n-1)`.
Experiment (Experimenter): Encode the extremal red graph as `blockGraph (k-1) (n-1)`
  on `Fin ((k-1)(n-1))`, with `Adj x y ↔ x ≠ y ∧ x/s = y/s`.  Show both monochromatic
  patterns are absent.
Analysis (Analyst): The "no red tree" direction is the substantive one: it needs that
  a graph homomorphism preserves reachability, so the connected tree lands inside a
  single block of size `n-1 < n`, contradicting injectivity.  The "no blue clique"
  direction is a pigeonhole on the `k-1` block indices.
Critique (Critic): The argument uses only connectivity of `T`, not acyclicity; we keep
  the `IsTree` hypothesis to stay faithful to the problem statement, but record that
  connectivity suffices (`chvatal_lower_bound_connected`).
Synthesis (PI): Lower bound proven for all `n, k`; pairs with the upper bound to pin
  down the all-ones case of Erdős 550.
-/


open SimpleGraph

open Erdos550







/-
The fiber of `blk` over a fixed block index `c` has at most `s` vertices.
-/

/-
**No red tree.**  A connected graph `T` on `n` vertices admits no copy inside
`blockGraph b s` when `s < n`: a hom preserves reachability, so the whole image
lands in a single block of size `≤ s`, contradicting injectivity.
-/

/-
**No blue clique.**  The complete graph `K_k` on `k` vertices admits no copy
inside `(blockGraph b s)ᶜ` when `b < k`: such a copy would inject the `k` vertices
into the `b` block indices.
-/

/-
**Lower bound for the all-ones case (connectivity form).**
For every connected graph `T` on `n` vertices and every `k ≥ 1`, the colouring
`blockGraph (k-1) (n-1)` of `K_{(k-1)(n-1)}` has neither a red `T` nor a blue
`K_k`, hence `¬ RamseyArrows ((k-1)(n-1)) T K_k`.
-/
theorem chvatal_lower_bound_connected {n : ℕ} (T : SimpleGraph (Fin n))
    (hT : T.Connected) {k : ℕ} (hk : 1 ≤ k) :
    ¬ RamseyArrows ((k - 1) * (n - 1)) T (⊤ : SimpleGraph (Fin k)) := by
  obtain a | a := Nat.eq_zero_or_pos n <;> simp_all +decide;
  · cases n <;> simp_all +decide [ SimpleGraph.connected_iff_exists_forall_reachable ];
  · intro h;
    convert no_red_connected T hT ( Nat.sub_lt a zero_lt_one ) <| h _ |> Or.resolve_right <| no_blue_clique <| Nat.sub_lt hk zero_lt_one



open Erdos550 in
theorem solution{n : ℕ} (T : SimpleGraph (Fin n)) (hT : T.IsTree)
    {k : ℕ} (hk : 1 ≤ k) :
    ¬ RamseyArrows ((k - 1) * (n - 1)) T (⊤ : SimpleGraph (Fin k)) :=
  chvatal_lower_bound_connected T hT.isConnected hk
