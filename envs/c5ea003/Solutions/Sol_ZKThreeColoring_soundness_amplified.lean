-- Prove2me | solution 1 for ZKThreeColoring.soundness_amplified
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:13:18.545324+00:00
-- url     : https://prove2.me/submissions/4840e2fa-4213-4269-8556-ba58de9a6887

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
omit [DecidableEq V] in
theorem solution{E : Finset (V × V)} (hE : E.Nonempty) (k : ℕ) :
    (1 - 1 / (E.card : ℝ)) ^ k ≤ Real.exp (-(k / E.card)) := by
  have hm : (0 : ℝ) < E.card := by exact_mod_cast card_pos.mpr hE
  have hle : (1 : ℝ) / E.card ≤ 1 := by
    rw [div_le_one hm]
    exact_mod_cast card_pos.mpr hE
  have hnn : (0 : ℝ) ≤ 1 - 1 / E.card := by linarith
  have hstep : 1 - 1 / (E.card : ℝ) ≤ Real.exp (-(1 / E.card)) := by
    have := Real.add_one_le_exp (-(1 / (E.card : ℝ)))
    linarith
  calc (1 - 1 / (E.card : ℝ)) ^ k ≤ (Real.exp (-(1 / E.card))) ^ k := by gcongr
    _ = Real.exp (-(k / E.card)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
