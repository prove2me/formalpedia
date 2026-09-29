-- Prove2me | Definitions.Def_Tropical_AnalogyCore
-- name    : Tropical_AnalogyCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:16.748688+00:00
-- url     : https://prove2.me/theorems/f6c41f32-d1eb-406a-bb16-764c9007475b
-- title:
--   Aether Catalog definitions — Tropical_AnalogyCore
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.AnalogyCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/AnalogyCore.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.

# Analogy as a Mathematical Operation — Core Metric Theory

This file formalizes Hofstadter's idea (from *Fluid Concepts and Creative
Analogies*) of an *analogy* between two structures `A` and `B` as a pair of
maps `F : A → B` and `G : B → A` such that the composite `G ∘ F` approximates
the identity on `A`.  We measure the quality of an analogy by its
*distortion*: the largest displacement `dist a (G (F a))`.

## Main results

* `Analogy.id_fidelity`     — the identity ("copycat") analogy has zero distortion.
* `Analogy.fidelity_zero_iff` — zero distortion characterises `G ∘ F = id`.
* `Analogy.fidelity_mono`   — distortion bounds are monotone.
* `Analogy.fidelity_nonneg` — distortion is always non-negative.
* `Analogy.comp_fidelity`   — **good analogies compose**: distortion is
  subadditive under a Lipschitz condition (a triangle inequality for analogies).
* `Analogy.exists_perfect_oneSided_not_equiv` — **disproof of a bold conjecture**:
  a perfect one-directional analogy (`G ∘ F = id_A`) need NOT be an equivalence
  (`F ∘ G ≠ id_B` in general).
-/

namespace TropicalAnalogy

open Metric

variable {A B C : Type*}

/-- An **analogy** between structures `A` and `B`: a forward map `toFun : A → B`
together with a backward map `invFun : B → A`.  No compatibility is assumed a
priori; the quality of the analogy is measured separately. -/
structure Analogy (A B : Type*) where
  toFun : A → B
  invFun : B → A

namespace Analogy

/-- The identity analogy on a structure (Hofstadter's *copycat*: `A = B` and both
maps are the identity). -/
def id (A : Type*) : Analogy A A := ⟨_root_.id, _root_.id⟩

/-- Composition of analogies: forward maps compose forwards, backward maps
compose backwards. -/
def comp (g : Analogy B C) (f : Analogy A B) : Analogy A C :=
  ⟨g.toFun ∘ f.toFun, f.invFun ∘ g.invFun⟩

/-- An analogy `f` has **fidelity `ε`** (distortion at most `ε`) if the round
trip `G ∘ F` moves every point of `A` by at most `ε`. -/
def IsFidelity [PseudoMetricSpace A] (f : Analogy A B) (ε : ℝ) : Prop :=
  ∀ a : A, dist a (f.invFun (f.toFun a)) ≤ ε

/-
The copycat/identity analogy is perfect: it has fidelity `0`.
-/

/-
Fidelity bounds are monotone in `ε`.
-/

/-
On a nonempty structure, any achievable fidelity bound is non-negative;
`0` is therefore the optimal (minimal) distortion.
-/

/-
**Zero distortion characterises a perfect left-inverse.** On a genuine
metric space, an analogy has fidelity `0` iff `G ∘ F` is the identity on `A`.
-/

/-
**Good analogies compose (triangle inequality for analogies).**
If `f : A → B` has fidelity `εf`, `g : B → C` has fidelity `εg`, and the
backward map `f.invFun` is `L`-Lipschitz (`L ≥ 0`), then the composite analogy
`g ∘ f` has fidelity `εf + L * εg`.  Thus a sequence of good analogies yields a
good analogy, with controlled accumulated distortion.
-/

/-
**Disproof of the "perfect analogy is an equivalence" conjecture.**
There is an analogy with *zero* distortion in the forward-then-back direction
(`G ∘ F = id_A`, since `A = PUnit` is a single point) whose other composite
`F ∘ G` is not the identity on `B = ℝ`.  Hence a perfect one-sided analogy need
not be a genuine isomorphism of structures.
-/

end Analogy

end TropicalAnalogy


