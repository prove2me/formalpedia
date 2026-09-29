-- Prove2me | Definitions.Def_Novelty_ErdosProblem550Base
-- name    : Novelty_ErdosProblem550Base
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:22:30.175142+00:00
-- url     : https://prove2.me/theorems/e1d892b6-cf08-42ff-9369-62c9af6d70fc
-- title:
--   Aether Catalog definitions — Novelty_ErdosProblem550Base
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ErdosProblem550Base`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ErdosProblem550Base.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ErdosProblem550Chvatal
/-
# Erdős Problem 550 — multipartite framework and the exact base case

This file complements `ErdosProblem550Chvatal.lean`.  It records the structural
facts about complete multipartite graphs that underlie Erdős Problem 550, and
proves the **exact base case** of the conjecture's hierarchy:

  `R(T, K_{1,1}) = n`   for every `n`-vertex tree `T`.

Here `K_{1,1} = K₂` is a single edge, and `R(T, K_{1,1})` is exactly the quantity
`R(T, K_{m₁,m₂})` appearing on the right-hand side of the Erdős–550 bound in the
all-ones case `m₁ = m₂ = 1`.  Combined with `ErdosProblem550Chvatal`, this pins
down the base term of the conjectured recursion.

We also record the **all-ones identification** `K_{1,…,1} ≅ K_k`: the complete
multipartite graph all of whose parts have size one is the complete graph, the
fact that turns the all-ones case of Erdős 550 into Chvátal's theorem.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): `R(T, K₂) = n` exactly, with the lower bound supplied by
  the disjoint-clique construction of the companion file and the upper bound by the
  dichotomy "a colouring of Kₙ is either all-red (so contains the tree) or has a blue
  edge".
Experiment (Experimenter): Formalise `RamseyArrows n T K₂` via the dichotomy, and read
  off the lower bound from `chvatal_lower_bound` specialised to `k = 2`.
Analysis (Analyst): The upper bound only needs `T ⊑ ⊤` (every graph embeds in the
  complete graph on the same vertex set) and the equivalence "blue edge ↔ K₂ ⊑ blue".
  No acyclicity of `T` is needed for the upper bound; the tree hypothesis enters only
  through the lower bound (which needs connectivity and `n ≥ 1`).
Critique (Critic): The all-ones identification must be stated as genuine mutual
  containment / isomorphism, not a definitional rename, to avoid a trivial theorem.
Synthesis (PI): The base case `R(T,K_{1,1}) = n` is exact and pairs with the general
  multipartite containment lemmas to frame the inductive structure of Erdős 550.
-/


open SimpleGraph

namespace Erdos550

/-- The complete multipartite graph `K_{m₀,…,m_{k-1}}` with parts indexed by `Fin k`,
the `i`-th part having `m i` vertices. -/
abbrev Kmultipartite {k : ℕ} (m : Fin k → ℕ) : SimpleGraph ((i : Fin k) × Fin (m i)) :=
  completeMultipartiteGraph (fun i => Fin (m i))


/-
**All-ones identification (≤ direction).**  `K_k` embeds into the complete
multipartite graph all of whose `k` parts have size one.
-/

/-
**All-ones identification (≥ direction).**  The complete multipartite graph all
of whose `k` parts have size one embeds into `K_k`. Together with
`completeGraph_isContained_allOnes` this expresses `K_{1,…,1} ≅ K_k`.
-/


/-
**Base-case upper bound.**  Every red/blue colouring of `Kₙ` either is all red
(hence contains the `n`-vertex graph `T` as a red copy, since `T ⊑ Kₙ`) or has a
blue edge (a blue `K₂`).  Thus `R(T, K₂) ≤ n`.
-/


end Erdos550


