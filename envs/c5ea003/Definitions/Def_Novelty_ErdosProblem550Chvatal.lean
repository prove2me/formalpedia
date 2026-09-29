-- Prove2me | Definitions.Def_Novelty_ErdosProblem550Chvatal
-- name    : Novelty_ErdosProblem550Chvatal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:21:52.880695+00:00
-- url     : https://prove2.me/theorems/a7cb0c0c-0ba7-4e54-9649-fb31cc2b7219
-- title:
--   Aether Catalog definitions — Novelty_ErdosProblem550Chvatal
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ErdosProblem550Chvatal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ErdosProblem550Chvatal.lean by skeleton subtraction
import Mathlib
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

namespace Erdos550

/-- The two-colour "arrow" relation for general graph patterns:
`RamseyArrows N T H` holds when every red/blue colouring of the complete graph on
`Fin N` (encoded by its red subgraph `G`, blue being the complement `Gᶜ`) contains
a red copy of `T` or a blue copy of `H`. -/
def RamseyArrows (N : ℕ) {α β : Type} (T : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∀ G : SimpleGraph (Fin N), T ⊑ G ∨ H ⊑ Gᶜ

/-- The extremal red graph: a disjoint union of `b` cliques, each on `s` vertices.
Two vertices of `Fin (b*s)` are adjacent iff they are distinct and lie in the same
block `⌊x/s⌋`. -/
def blockGraph (b s : ℕ) : SimpleGraph (Fin (b * s)) where
  Adj x y := x ≠ y ∧ x.val / s = y.val / s
  symm := by intro x y h; exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun x h => h.1 rfl⟩

/-- The block index of a vertex. -/
def blk (b s : ℕ) (x : Fin (b * s)) : ℕ := x.val / s




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


end Erdos550


