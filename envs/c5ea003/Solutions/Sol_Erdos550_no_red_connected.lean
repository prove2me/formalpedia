-- Prove2me | solution 1 for Erdos550.no_red_connected
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:05:24.403451+00:00
-- url     : https://prove2.me/submissions/21e95d26-1637-4042-824c-af43073486f8

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





/-- Reachable vertices lie in the same block. -/
theorem blk_eq_of_reachable (b s : ℕ) {x y : Fin (b * s)}
    (h : (blockGraph b s).Reachable x y) : blk b s x = blk b s y := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact hadj.2.trans ih


/-
The fiber of `blk` over a fixed block index `c` has at most `s` vertices.
-/
theorem fiber_card_le (b s c : ℕ) :
    (Finset.univ.filter (fun x : Fin (b * s) => blk b s x = c)).card ≤ s := by
  by_contra h_contra;
  obtain ⟨x₁, x₂, hx₁, hx₂, hxs⟩ : ∃ x₁ x₂ : Fin (b * s), blk b s x₁ = c ∧ blk b s x₂ = c ∧ x₁ ≠ x₂ ∧ x₁.val % s = x₂.val % s := by
    by_contra! h_contra' ; simp_all +decide ;
    exact absurd ( Finset.card_le_card ( show Finset.image ( fun x : Fin ( b * s ) => ( x : ℕ ) % s ) ( Finset.filter ( fun x : Fin ( b * s ) => blk b s x = c ) Finset.univ ) ⊆ Finset.range s from Finset.image_subset_iff.2 fun x hx => Finset.mem_range.2 <| Nat.mod_lt _ <| Nat.pos_of_ne_zero <| by aesop_cat ) ) ( by rw [ Finset.card_image_of_injOn <| fun x hx y hy hxy => by contrapose! hxy; aesop ] ; simpa using h_contra );
  have h_eq : x₁.val = s * c + (x₁.val % s) ∧ x₂.val = s * c + (x₂.val % s) := by
    exact ⟨ by rw [ ← hx₁, blk ] ; rw [ Nat.div_add_mod ], by rw [ ← hx₂, blk ] ; rw [ Nat.div_add_mod ] ⟩;
  exact hxs.1 ( Fin.ext <| by linarith )

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
theorem solution{n b s : ℕ} (T : SimpleGraph (Fin n)) (hT : T.Connected)
    (hsn : s < n) : ¬ (T ⊑ blockGraph b s) := by
  rintro ⟨ f, hf ⟩;
  -- Since $T$ is connected, the image of $f$ is contained in a single block of $blockGraph b s$.
  have h_block : ∃ c : ℕ, ∀ x : Fin n, blk b s (f x) = c := by
    have h_block : ∀ x y : Fin n, (blockGraph b s).Reachable (f x) (f y) := by
      intro x y; have := hT x y; simp_all +decide [ SimpleGraph.Reachable ] ;
      exact ⟨ this.some.map f ⟩;
    exact ⟨ blk b s ( f ⟨ 0, by linarith ⟩ ), fun x => blk_eq_of_reachable b s ( h_block _ _ ) ⟩;
  obtain ⟨ c, hc ⟩ := h_block;
  have h_card : (Finset.univ.image f).card ≤ (Finset.univ.filter (fun x : Fin (b * s) => blk b s x = c)).card := by
    exact Finset.card_le_card fun x hx => by aesop;
  exact absurd h_card ( by rw [ Finset.card_image_of_injective _ hf ] ; simpa using by linarith [ fiber_card_le b s c ] )
