-- Prove2me | Theorems.Thm_JokeSurpriseAlgebra_humor_union_ge_left
-- name    : JokeSurpriseAlgebra.humor_union_ge_left
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:56:58.150552+00:00
-- url     : https://prove2.me/theorems/1e4320f9-11c8-4c3a-9674-00b9fbf579f9
-- title:
--   Juxtaposition is inflationary (left).
-- statement:
--   **Juxtaposition is inflationary (left).** Combining a setup with another can only
--   increase its surprise.
--
--   ```lean
--   theorem JokeSurpriseAlgebra.humor_union_ge_left(S T : Finset ℝ) (hS : S.Nonempty) :
--       humor S hS ≤ humor (S ∪ T) hS.inl := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/JokeSurpriseAlgebra.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/JokeSurpriseAlgebra.lean#L83

-- Thm stub generated from Applications/JokeSurpriseAlgebra.lean
import Mathlib
import Definitions.Def_Applications_JokeSurpriseAlgebra

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

open JokeSurpriseAlgebra

theorem JokeSurpriseAlgebra.humor_union_ge_left(S T : Finset ℝ) (hS : S.Nonempty) :
    humor S hS ≤ humor (S ∪ T) hS.inl := by sorry
