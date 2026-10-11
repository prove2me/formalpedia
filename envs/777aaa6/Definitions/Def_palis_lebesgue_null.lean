-- Prove2me | Definitions.Def_palis_lebesgue_null
-- name    : palis_lebesgue_null
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T02:50:53.94242+00:00
-- url     : https://prove2.me/theorems/3bd6264d-23a5-44cf-a5ff-8d47b647401e
-- title:
--   Lebesgue-null subsets of a manifold
-- statement:
--   Let $M$ be a topological manifold modelled on $\mathbb R^n$, with a given atlas of charts $e:U_e\to\mathbb R^n$. A subset $s\subset M$ is **Lebesgue-null** if for every chart $e$ of the atlas
--   $$\mathrm{Leb}_n\big(e(s\cap U_e)\big)=0,$$
--   where $\mathrm{Leb}_n$ is Lebesgue (outer) measure on $\mathbb R^n$.
--
--   This is the notion of "Lebesgue almost all" and "positive Lebesgue measure" used in the source. For a $C^1$ atlas it does not depend on the choice of atlas, since $C^1$ maps send null sets to null sets.
--
--   **Formalization Note** `PalisConjecture.IsLebesgueNull n s` uses `MeasureTheory.volume` on `EuclideanSpace ℝ (Fin n)` and quantifies over the charts in `atlas`. The dimension `n` is an explicit argument.
-- source:
--   Open Problem Garden, "Jacob Palis Conjecture (Finitude of Attractors) (Dynamical Systems)", posted by Jailton Viana, April 24, 2013, https://www.openproblemgarden.org/op/jacob_palis_conjecture_finitude_of_attractors_dynamical_systems (Conjecture box and the Definition of attractor below it); bibliography: C. Bonatti, L. J. Diaz, M. Viana, Dynamics Beyond Uniform Hyperbolicity, Encyclopaedia of Mathematical Sciences 102, Springer, 2005.

import Mathlib

/-!
# Lebesgue-null subsets of a manifold

A subset `s` of a manifold `M` modeled on `ℝⁿ` (as `EuclideanSpace ℝ (Fin n)`) has
*Lebesgue measure zero* if its image in every chart of the atlas has Lebesgue measure zero.
-/

namespace PalisConjecture

/-- `s ⊆ M` is Lebesgue-null: for every chart `e` of the atlas of `M`, the image
`e '' (s ∩ e.source)` has Lebesgue (outer) measure zero in `ℝⁿ`. -/
def IsLebesgueNull (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (s : Set M) : Prop :=
  ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) M,
    MeasureTheory.volume (e '' (s ∩ e.source)) = 0

end PalisConjecture


