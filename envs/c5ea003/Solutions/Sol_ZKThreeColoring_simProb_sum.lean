-- Prove2me | solution 1 for ZKThreeColoring.simProb_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:13:18.04881+00:00
-- url     : https://prove2.me/submissions/ca33f2f5-7a3b-4fdb-b810-f1635bcc747c

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


variable [DecidableEq V]





/-! ## Perfect zero knowledge

The verifier's view of a single round is the triple `(e, x, y)`: the edge it challenged
and the two colors that were opened. We compute its distribution exactly. -/











/-! ## The soundness bound is tight: the instance `K₄`

The complete graph on four vertices is not 3-colourable, yet a cheating prover can commit
to an assignment that survives all but one of its six edges. So the bound
`acceptProb ≤ 1 - 1/|E|` of `acceptProb_le_one_sub_inv` cannot be improved. -/







open ZKThreeColoring in
theorem solution[Fintype V] {E : Finset (V × V)} (hE : E.Nonempty) :
    ∑ t : (V × V) × Fin 3 × Fin 3, simProb E t = 1 := by
  have hm : (E.card : ℝ) ≠ 0 := by
    have : 0 < E.card := card_pos.mpr hE
    positivity
  have hcolors : ∑ p : Fin 3 × Fin 3, (if p.1 ≠ p.2 then (1 : ℝ) / 6 else 0) = 1 := by
    rw [Fintype.sum_prod_type]
    simp [Fin.sum_univ_three]
    norm_num
  have hedges : ∑ e : V × V, (if e ∈ E then (1 : ℝ) / E.card else 0) = 1 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    field_simp
  calc ∑ t : (V × V) × Fin 3 × Fin 3, simProb E t
      = ∑ e : V × V, ∑ p : Fin 3 × Fin 3,
          (if e ∈ E then (1 : ℝ) / E.card else 0) * (if p.1 ≠ p.2 then 1 / 6 else 0) := by
        rw [Fintype.sum_prod_type]; rfl
    _ = ∑ e : V × V, (if e ∈ E then (1 : ℝ) / E.card else 0) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← Finset.mul_sum, hcolors, mul_one]
    _ = 1 := hedges
