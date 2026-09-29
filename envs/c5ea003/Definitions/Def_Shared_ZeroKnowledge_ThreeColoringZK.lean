-- Prove2me | Definitions.Def_Shared_ZeroKnowledge_ThreeColoringZK
-- name    : Shared_ZeroKnowledge_ThreeColoringZK
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:16:30.63832+00:00
-- url     : https://prove2.me/theorems/5e7743c3-5956-430e-ad50-15465a28b715
-- title:
--   Aether Catalog definitions — Shared_ZeroKnowledge_ThreeColoringZK
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ZeroKnowledge.ThreeColoringZK`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ZeroKnowledge/ThreeColoringZK.lean by skeleton subtraction
import Mathlib

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

namespace ZKThreeColoring

variable {V : Type*}

/-! ## The protocol -/

/-- `c` is a proper 3-coloring for the edge list `E`: the endpoints of every edge of `E`
receive different colors. -/
def IsProper (E : Finset (V × V)) (c : V → Fin 3) : Prop := ∀ e ∈ E, c e.1 ≠ c e.2

/-- The graph with edge list `E` is 3-colorable. -/
def ThreeColorable (E : Finset (V × V)) : Prop := ∃ c : V → Fin 3, IsProper E c

/-- The edges on which the verifier accepts a committed assignment `f`. -/
def acceptEdges (E : Finset (V × V)) (f : V → Fin 3) : Finset (V × V) :=
  E.filter fun e => f e.1 ≠ f e.2

/-- The probability that the verifier accepts the committed assignment `f`, i.e. the
fraction of edges whose endpoints receive distinct values. -/
noncomputable def acceptProb (E : Finset (V × V)) (f : V → Fin 3) : ℝ :=
  (acceptEdges E f).card / E.card




/-! ## Completeness -/



/-! ## Soundness -/


variable [DecidableEq V]





/-! ## Perfect zero knowledge

The verifier's view of a single round is the triple `(e, x, y)`: the edge it challenged
and the two colors that were opened. We compute its distribution exactly. -/


/-- The distribution of the verifier's view `(e, x, y)` in a real execution with the
witness `c`: a uniform edge together with the two colors opened by a uniformly random
recoloring of `c` (there are `6` such recolorings). -/
noncomputable def viewProb (E : Finset (V × V)) (c : V → Fin 3)
    (t : (V × V) × Fin 3 × Fin 3) : ℝ :=
  (if t.1 ∈ E then (1 : ℝ) / E.card else 0) *
    (((univ.filter fun π : Equiv.Perm (Fin 3) =>
        π (c t.1.1) = t.2.1 ∧ π (c t.1.2) = t.2.2).card : ℝ) / 6)

/-- The simulator: it knows no witness at all, and simply outputs a uniformly random edge
together with a uniformly random *ordered pair of distinct colors*. -/
noncomputable def simProb (E : Finset (V × V)) (t : (V × V) × Fin 3 × Fin 3) : ℝ :=
  (if t.1 ∈ E then (1 : ℝ) / E.card else 0) * (if t.2.1 ≠ t.2.2 then 1 / 6 else 0)


/-- Statistical distance between two real-valued distributions on a finite type. -/
noncomputable def statDist {Ω : Type*} [Fintype Ω] (μ ν : Ω → ℝ) : ℝ :=
  (1 / 2) * ∑ x : Ω, |μ x - ν x|






/-! ## The soundness bound is tight: the instance `K₄`

The complete graph on four vertices is not 3-colourable, yet a cheating prover can commit
to an assignment that survives all but one of its six edges. So the bound
`acceptProb ≤ 1 - 1/|E|` of `acceptProb_le_one_sub_inv` cannot be improved. -/

/-- The edge list of the complete graph `K₄`. -/
def K4edges : Finset (Fin 4 × Fin 4) := {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)}



/-- The best cheating assignment for `K₄`: it repeats the colour `0` on the edge `(0,3)`
only. -/
def K4cheat : Fin 4 → Fin 3 := ![0, 1, 2, 0]


end ZKThreeColoring


