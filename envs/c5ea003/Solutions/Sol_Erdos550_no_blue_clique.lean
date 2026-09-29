-- Prove2me | solution 1 for Erdos550.no_blue_clique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:05:23.734772+00:00
-- url     : https://prove2.me/submissions/bd739474-4d0d-482d-80a1-bd917529d500

-- Sol generated from Novelty/ErdosProblem550Chvatal.lean
import Mathlib
import Definitions.Def_Novelty_ErdosProblem550Chvatal
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



open Erdos550 in
theorem solution{k b s : ℕ} (hbk : b < k) :
    ¬ ((⊤ : SimpleGraph (Fin k)) ⊑ (blockGraph b s)ᶜ) := by
  by_contra! h_contra;
  -- Let $f$ be the homomorphism from the complete graph on $k$ vertices to the complement of the block graph.
  obtain ⟨f, hf_inj, hf_hom⟩ : ∃ f : Fin k → Fin (b * s), Function.Injective f ∧ ∀ i j, i ≠ j → ¬(blockGraph b s).Adj (f i) (f j) := by
    obtain ⟨ f, hf ⟩ := h_contra;
    use f;
    exact ⟨ hf, fun i j hij h => by have := f.map_rel ( show ( ⊤ : SimpleGraph ( Fin k ) ).Adj i j from by aesop ) ; aesop ⟩;
  -- Consider the function $g : Fin k → Fin b$ defined by $g(i) = blk b s (f i)$.
  set g : Fin k → Fin b := fun i => ⟨blk b s (f i), by
    exact Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt ( f i ) ] ;⟩
  generalize_proofs at *;
  exact absurd ( Fintype.card_le_of_injective g ( fun i j hij => Classical.not_not.1 fun hi => hf_hom i j hi <| by
    exact ⟨ hf_inj.ne hi, by aesop ⟩ ) ) ( by simpa using by linarith )
