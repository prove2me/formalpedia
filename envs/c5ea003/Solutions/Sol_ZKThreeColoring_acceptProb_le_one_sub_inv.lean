-- Prove2me | solution 1 for ZKThreeColoring.acceptProb_le_one_sub_inv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:13:17.519172+00:00
-- url     : https://prove2.me/submissions/f6de72f5-618e-429e-a5aa-518f8f55eb3e

-- Sol generated from Shared/ZeroKnowledge/ThreeColoringZK.lean
import Mathlib
import Definitions.Def_Shared_ZeroKnowledge_ThreeColoringZK

/-!
# The GMW zero-knowledge proof for graph 3-colorability

This file formalizes the Goldreich–Micali–Wigderson interactive proof that a graph is
3-colorable, and proves its three defining properties in a purely combinatorial,
quantitative form: every probability is realized as a ratio of cardinalities of explicit
finite sets.

The protocol on a graph with vertex set `V` and edge list `E : Finset (V × V)`:

* the prover holds a proper 3-coloring `c : V → Fin 3`, picks a uniformly random
  permutation `π` of the three colors and commits to `π ∘ c` vertex by vertex;
* the verifier picks a uniformly random edge `e ∈ E`, asks the prover to open the two
  endpoints, and accepts iff the two revealed colors differ.

## Main results

* `acceptProb_eq_one_of_isProper` — perfect completeness.
* `acceptProb_le_one_sub_inv` — soundness: if the graph is *not* 3-colorable then no
  committed assignment is accepted with probability more than `1 - 1/|E|`.
* `soundness_amplified` — `k` independent repetitions give error at most `exp (-k/|E|)`.
* `zk_perfect` — perfect zero knowledge: the distribution of the verifier's view is
  *equal* to the output distribution of the witness-free simulator `simProb`.
* `zk_statDist_eq_zero` — the same statement phrased with statistical distance.
* `zk_witness_indistinguishable` — two different proper colorings induce literally the
  same view distribution, so the transcript carries no information about the witness.

The heart of the zero-knowledge argument is `perm3_pair_count`: the symmetric group on
three colors acts *sharply transitively* on ordered pairs of distinct colors, so opening
an edge of a randomly recolored proper coloring reveals a uniformly random ordered pair
of distinct colors, independently of the witness.
-/

open Finset

open ZKThreeColoring

variable {V : Type*}

/-! ## The protocol -/








/-! ## Completeness -/



/-! ## Soundness -/

/-- If the graph is not 3-colorable, every committed assignment `f` fails on at least one
edge. -/
theorem exists_bad_edge {E : Finset (V × V)} (h : ¬ ThreeColorable E) (f : V → Fin 3) :
    ∃ e ∈ E, f e.1 = f e.2 := by
  by_contra hcon
  push_neg at hcon
  exact h ⟨f, fun e he => hcon e he⟩

variable [DecidableEq V]





/-! ## Perfect zero knowledge

The verifier's view of a single round is the triple `(e, x, y)`: the edge it challenged
and the two colors that were opened. We compute its distribution exactly. -/











/-! ## The soundness bound is tight: the instance `K₄`

The complete graph on four vertices is not 3-colourable, yet a cheating prover can commit
to an assignment that survives all but one of its six edges. So the bound
`acceptProb ≤ 1 - 1/|E|` of `acceptProb_le_one_sub_inv` cannot be improved. -/







open ZKThreeColoring in
theorem solution{E : Finset (V × V)} (hE : E.Nonempty)
    (h : ¬ ThreeColorable E) (f : V → Fin 3) :
    acceptProb E f ≤ 1 - 1 / E.card := by
  obtain ⟨e₀, he₀, hbad⟩ := exists_bad_edge h f
  have hsub : acceptEdges E f ⊆ E.erase e₀ := by
    intro e he
    rw [acceptEdges, mem_filter] at he
    exact mem_erase.mpr ⟨by rintro rfl; exact he.2 hbad, he.1⟩
  have hcard : (acceptEdges E f).card + 1 ≤ E.card := by
    have h1 : (acceptEdges E f).card ≤ (E.erase e₀).card := card_le_card hsub
    have h2 : (E.erase e₀).card = E.card - 1 := card_erase_of_mem he₀
    have h3 : 1 ≤ E.card := card_pos.mpr hE
    omega
  have hm : (0 : ℝ) < E.card := by exact_mod_cast card_pos.mpr hE
  have h1 : ((acceptEdges E f).card : ℝ) ≤ (E.card : ℝ) - 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr hcard
    push_cast at this
    linarith
  rw [acceptProb, div_le_iff₀ hm]
  have hmul : (1 - 1 / (E.card : ℝ)) * E.card = (E.card : ℝ) - 1 := by field_simp
  rw [hmul]
  exact h1
