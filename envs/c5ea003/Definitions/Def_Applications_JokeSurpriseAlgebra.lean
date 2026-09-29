-- Prove2me | Definitions.Def_Applications_JokeSurpriseAlgebra
-- name    : Applications_JokeSurpriseAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:23.584987+00:00
-- url     : https://prove2.me/theorems/c0ba8d9f-2a00-466f-804d-6474095527c8
-- title:
--   Aether Catalog definitions — Applications_JokeSurpriseAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.JokeSurpriseAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/JokeSurpriseAlgebra.lean by skeleton subtraction
import Mathlib

/-!
# The Algebra of Surprise: Combining and Refining Jokes

This file extends the metric theory of surprise (see `JokeHumorMetric`) and the
universal/terminal theory of resolutions (see `UniversalJoke`) with the *algebra* of
how surprise behaves when jokes are **combined** and **refined**.

A "setup" is modelled by a finite nonempty configuration of resolutions `S ⊆ ℝ`, laid
out along a single interpretive axis, and its **surprise** is the range

`humor S = max' S - min' S`,

the gap between its most divergent and most conservative reading. Two setups can be
combined by juxtaposition (`∪`) — telling both jokes together — or intersected
(`∩`) — restricting to their shared readings. This file characterises how surprise
transforms under these operations, and packages the whole thing categorically.

## Combination laws

* `humor_union_eq` : the surprise of a combined setup is determined *entirely* by the
  four extremal resolutions of the two parts.
* `humor_union_ge_left` / `humor_union_ge_right` : combining jokes never decreases
  surprise — juxtaposition is *inflationary*.
* `humor_union_le_add_of_inter` : **subadditivity under shared context.** If the two
  setups share a common resolution (a "pivot" both jokes pass through), the combined
  surprise is at most the sum of the individual surprises. This is the lax structure
  map of surprise viewed as a lax monoidal functor for the union monoidal structure.
* `humor_inter_le_left` : restricting to shared readings can only decrease surprise.

## Categorical packaging

Setups are ordered by refinement (`⊆`), which makes `Setup` a (thin) category. The
central structural result is:

* `surpriseFunctor` : surprise is a **functor** `Setup ⥤ ℝ` from the category of
  setups (ordered by refinement) to the real line (ordered by magnitude), and
* `surprise_of_refinement` : every refinement of setups is sent to an inequality of
  surprises — functoriality is exactly the statement that "a funnier reading of a
  funnier setup stays funnier".

-- !-- Lab Notes -- !--
Hypothesis: surprise is not merely a numerical invariant but an *algebraic* one — it
interacts predictably with the natural operations on setups (union, intersection,
refinement), and these interactions are the shadow of a functorial/lax-monoidal
structure.

Experiment: model setups as nonempty `Finset ℝ`. Each combination law was reduced to
`Finset.max'_union`, `Finset.min'_union`, and the order lemmas `le_max'` / `min'_le`,
then discharged by `linarith` (after a `max_def`/`min_def` case split for the
subadditivity bound). The functor was obtained from monotonicity of `humor` via
`Monotone.functor`.

Analysis: `humor_union_le_add_of_inter` is the load-bearing result: subadditivity
*fails* in general (two far-apart jokes have combined surprise far exceeding the sum of
their individual surprises), but holds precisely when the setups share a pivot. This is
the categorical fingerprint of a lax monoidal — not strong monoidal — structure.

Critique: the model is one-dimensional, so `min'`/`max'` genuinely bracket each set.
The shared-context hypothesis in `humor_union_le_add_of_inter` is necessary, not
cosmetic: without it the bound is false.

Synthesis: surprise is a monotone functor from the poset of setups to the reals, lax
monoidal for juxtaposition with shared context — combining jokes inflates surprise,
refining setups is respected, and shared context tames the growth.
-/

open CategoryTheory Finset

namespace JokeSurpriseAlgebra

/-- The **surprise** of a setup: the gap between its most divergent resolution
(`max'`) and its most conservative resolution (`min'`). -/
noncomputable def humor (S : Finset ℝ) (h : S.Nonempty) : ℝ := S.max' h - S.min' h






/-! ### Surprise as a functor

We now package the monotonicity of surprise categorically. Setups form a thin category
under refinement (`⊆`); the reals form a thin category under magnitude (`≤`). Surprise
is a functor between them. -/

/-- A **setup**: a nonempty finite configuration of resolutions. -/
def Setup : Type := {S : Finset ℝ // S.Nonempty}

/-- Setups are ordered by **refinement**: `S ≤ T` means every resolution of `S` is a
resolution of `T`. This makes `Setup` a (thin) category. -/
instance : Preorder Setup := Subtype.preorder _

/-- Surprise as a bare function on setups. -/
noncomputable def humorS (S : Setup) : ℝ := S.1.max' S.2 - S.1.min' S.2

/-- **Surprise is monotone under refinement.** -/
theorem humorS_monotone : Monotone humorS := by
  rintro ⟨S, hS⟩ ⟨T, hT⟩ (hsub : S ⊆ T)
  have hmax : S.max' hS ≤ T.max' hT := T.le_max' _ (hsub (S.max'_mem hS))
  have hmin : T.min' hT ≤ S.min' hS := T.min'_le _ (hsub (S.min'_mem hS))
  simp only [humorS]; linarith

/-- **Surprise is a functor** from the category of setups (ordered by refinement) to
the real line (ordered by magnitude). -/
noncomputable def surpriseFunctor : Setup ⥤ ℝ := humorS_monotone.functor


end JokeSurpriseAlgebra


