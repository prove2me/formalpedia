-- Prove2me | solution 1 for HeadComposition.Representable.add
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:55:26.453979+00:00
-- url     : https://prove2.me/submissions/fabd2b02-5fd6-4648-868b-c1154b8a7124

-- Sol generated from MachineLearning/TransformerUniversality/HeadComposition.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_HeadComposition

/-!
# Compositional behaviour of head complexity

`Catalog/MachineLearning/TransformerUniversality/HeadComplexity.lean` characterizes the minimal
number of heads of a value-sum architecture computing a finite value table `f` as the rank of
that table.  The second next-cycle sub-conjecture of `FUTURE_DIRECTIONS.md` asked how this
resource behaves under composition.  This file settles it.

We repeat the definitions of that file (each catalog file is self-contained):
a *value-sum architecture with `H` heads* computes `model x = ∑ h : Fin H, c h x • v h`, with
arbitrary input-dependent scalar gates `c h` and input-independent value vectors `v h`.

Main results:

* `Representable.postcomp` / `minHeads_postcomp_le` — post-composition with a **linear**
  read-out never increases the head count;
* `minHeads_postcomp_of_injective` — and never decreases it either when the read-out is
  injective, because an injective linear map between vector spaces has a linear left inverse;
  hence head complexity is an invariant of the value table up to linear isomorphism;
* `minHeads_postcomp_zero` — the inequality really can be strict (the zero read-out), so
  injectivity is not a technical artifact;
* `Representable.add` / `minHeads_add_le` — **subadditivity**: heads of a sum of tasks are at
  most the sum of the heads, realized by concatenating the two head sets (`Fin.append`);
* `minHeads_smul_le`, `minHeads_precomp_le` — scaling the task and restricting the input
  domain do not increase head complexity;
* `minHeads_le_card` — the catalog's exact-lookup construction as an upper bound, which is
  also what makes `minHeads` a genuine minimum (the defining set is nonempty).

Together these say that `minHeads` is a *monotone, subadditive, linear-isomorphism invariant*
of the value table: exactly the formal properties one wants from a complexity measure, and the
properties needed to reason about stacked attention blocks rather than a single layer.
-/

open scoped BigOperators

open HeadComposition

variable {X X' Y Z : Type*} [Fintype X]




















open HeadComposition in
omit [Fintype X] in
theorem solution{f g : X → Y → ℝ} {H₁ H₂ : ℕ}
    (hf : Representable f H₁) (hg : Representable g H₂) :
    Representable (fun x => f x + g x) (H₁ + H₂) := by
  obtain ⟨c₁, v₁, h₁⟩ := hf
  obtain ⟨c₂, v₂, h₂⟩ := hg
  refine ⟨Fin.append c₁ c₂, Fin.append v₁ v₂, fun x => ?_⟩
  rw [Fin.sum_univ_add]
  have e₁ : ∑ i : Fin H₁, (Fin.append c₁ c₂) (Fin.castAdd H₂ i) x •
      (Fin.append v₁ v₂) (Fin.castAdd H₂ i) = ∑ i : Fin H₁, c₁ i x • v₁ i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.append_left, Fin.append_left]
  have e₂ : ∑ i : Fin H₂, (Fin.append c₁ c₂) (Fin.natAdd H₁ i) x •
      (Fin.append v₁ v₂) (Fin.natAdd H₁ i) = ∑ i : Fin H₂, c₂ i x • v₂ i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.append_right, Fin.append_right]
  rw [e₁, e₂, ← h₁ x, ← h₂ x]
