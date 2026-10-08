-- Prove2me | Theorems.Thm_YoungConventions_Perturbed_markov_chain_tree_formula
-- name    : YoungConventions.Perturbed.markov_chain_tree_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:59:10.648588+00:00
-- url     : https://prove2.me/theorems/bd147284-39dd-44e4-813c-8c20226128b4
-- title:
--   Markov chain tree formula: $\mu'_z = p'_z / \sum_x p'_x$ is the unique stationary distribution
-- statement:
--   Let $P'$ be the transition matrix of an aperiodic, irreducible Markov chain on a nonempty finite set $X$. For $z \in X$ let
--   $$p'_z = \sum_{T \in \mathcal T_z} \prod_{(x,y) \in T} P'_{xy},$$
--   where $\mathcal T_z$ is the set of $z$-trees (spanning in-trees directed toward $z$) on $X$. Then $p'_z > 0$ for every $z$, and
--   $$\mu'_z = \frac{p'_z}{\sum_{x \in X} p'_x}$$
--   is a stationary distribution of $P'$ ($\mu' P' = \mu'$), and it is the unique stationary distribution of $P'$.
--
--   This is the lemma of Freidlin and Wentzell (1984, Ch. 6, Lemma 3.1) that Young applies to $P^\varepsilon$ in the proof of Lemma 1: it writes $\mu^\varepsilon$ as a ratio of polynomials in the entries of $P^\varepsilon$, whose orders of magnitude are read off from the resistances.
--
--   **Formalization Note** Both hypotheses printed on the page (aperiodic and irreducible) are kept, although irreducibility suffices. Trees through zero entries are included in the sum and contribute $0$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, Appendix, proof of Lemma 1, p. 79 (PDF p. 24); Freidlin and Wentzell (1984), Random Perturbations of Dynamical Systems, Ch. 6, Lemma 3.1

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_InTree

open Finset

namespace YoungConventions.Perturbed

/-- The Markov chain tree formula (Freidlin–Wentzell 1984, Ch. 6, Lemma 3.1), as quoted in the proof
of Lemma 1 (Young 1993, Econometrica 61:57–84, Appendix, p. 79, PDF p. 24).

Let `P′` be the transition matrix of an aperiodic, irreducible Markov chain on the finite set
`X`, and for `z ∈ X` let `p′_z = ∑_{T ∈ 𝒯_z} ∏_{(x,y) ∈ T} P′_{xy}` (`treeWeight`). Then every
`p′_z` is positive, `μ′_z = p′_z / ∑_x p′_x` is a stationary distribution of `P′`, and it is the
unique stationary distribution of `P′`.

**Formalization Note.** Both hypotheses of the page (aperiodic and irreducible) are kept, although
irreducibility alone suffices. The state type is nonempty: on an empty type both conditions
hold vacuously, but no probability distribution can have total mass `1`. `z`-trees are in-trees
(edges point toward `z`), so for two states `p′_1 = P′_{21}` and `p′_2 = P′_{12}`. -/
theorem markov_chain_tree_formula {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (A : Matrix X X ℝ) (hA : A ∈ Matrix.rowStochastic ℝ X)
    (hirr : A.IsIrreducible) (hap : IsAperiodic A) :
    (∀ z, 0 < treeWeight A z) ∧
    IsStationaryDist A (fun z => treeWeight A z / ∑ x, treeWeight A x) ∧
    ∀ ν : X → ℝ, IsStationaryDist A ν → ν = fun z => treeWeight A z / ∑ x, treeWeight A x := by sorry

end YoungConventions.Perturbed
