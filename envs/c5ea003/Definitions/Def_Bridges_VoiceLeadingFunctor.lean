-- Prove2me | Definitions.Def_Bridges_VoiceLeadingFunctor
-- name    : Bridges_VoiceLeadingFunctor
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:46:48.15022+00:00
-- url     : https://prove2.me/theorems/ee2e73ca-4482-47b3-b80e-b2040bc99b7d
-- title:
--   Aether Catalog definitions — Bridges_VoiceLeadingFunctor
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.VoiceLeadingFunctor`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/VoiceLeadingFunctor.lean by skeleton subtraction
import Mathlib

/-!
# Voice-Leading as a Category with Functor to Lawvere Metric Spaces

This file constructs a **category** whose objects are equal-cardinality voicings
and whose morphisms are voice-leadings (permutation-based assignments), then
proves the fundamental **cost triangle inequality** that makes it a Lawvere metric.

## Main Results

* `VLF.VLHom.cost_comp_le` — Triangle inequality for composition of voice-leadings
* `VLF.VLHom.cost_id` — Identity morphism has zero cost
* `VLF.vlBundledLawvere` — Voice-leadings form a Lawvere metric space
* `VLF.vlDist_triangle` — Triangle inequality for minimum voice-leading distance

## Mathematical Significance

Voice-leading — the art of moving smoothly between chords — is shown to be
not merely a musical heuristic but a **functorial distance theory**: the cost
of voice-leading satisfies the enriched composition law of Lawvere metric spaces.
-/

open Finset BigOperators CategoryTheory

noncomputable section

namespace VLF

/-! ## Core Definitions -/

/-- A voicing of n notes is a function from Fin n to pitch classes in ℤ. -/
abbrev Voicing (n : ℕ) := Fin n → ℤ

/-- Voice-leading morphism: a permutation-based assignment between voicings. -/
structure VLHom {n : ℕ} (V W : Voicing n) where
  perm : Equiv.Perm (Fin n)

/-- Identity voice-leading. -/
def VLHom.id {n : ℕ} (V : Voicing n) : VLHom V V where
  perm := Equiv.refl _

/-- Composition of voice-leadings. -/
def VLHom.comp {n : ℕ} {V W U : Voicing n} (f : VLHom V W) (g : VLHom W U) :
    VLHom V U where
  perm := f.perm.trans g.perm

/-- Cost (total displacement) of a voice-leading. -/
def VLHom.cost {n : ℕ} {V W : Voicing n} (f : VLHom V W) : ℝ :=
  ∑ i : Fin n, |(V i : ℝ) - (W (f.perm i) : ℝ)|



/-
**Triangle inequality for voice-leading cost**: the cost of a composed
voice-leading is at most the sum of the individual costs.
This is the fundamental enriched composition law.
-/

/-! ## Minimum Voice-Leading Distance -/

/-- Minimum voice-leading distance. -/
def vlDist {n : ℕ} (V W : Voicing n) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).inf'
    Finset.univ_nonempty
    (fun σ => ∑ i : Fin n, |(V i : ℝ) - (W (σ i) : ℝ)|)



/-
Triangle inequality for minimum voice-leading distance.
-/

/-! ## Lawvere Metric Space -/



/-! ## Bridge: Cost as Categorical Distance -/



end VLF


