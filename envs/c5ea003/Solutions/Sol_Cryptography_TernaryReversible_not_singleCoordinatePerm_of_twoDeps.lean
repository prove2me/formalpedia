-- Prove2me | solution 1 for Cryptography.TernaryReversible.not_singleCoordinatePerm_of_twoDeps
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:10:24.367679+00:00
-- url     : https://prove2.me/submissions/14379219-b85d-45fd-af31-61a3477bf9d7

-- Sol generated from Cryptography/TernaryReversible/Core.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core

/-!
# Reversible ternary radius-one cellular automata: core framework

Alphabet `Fin 3`, local rules `g : Fin 3 → Fin 3 → Fin 3 → Fin 3` (a radius-one,
window-three rule) and the induced *global maps* on the finite cycle `ZMod n`:

`globalMap g s i = g (s (i-1)) (s i) (s (i+1))`.

A rule is **cycle-bijective** when its global map is bijective on *every* nonempty
finite cycle.  This file develops the general tools:

* `globalMap`, `CycleBijective`, `SingleCoordinatePerm`;
* `cycleBijective_of_decoder3` / `cycleBijective_of_decoder4R`: a *local decoder*
  (a local inverse rule, of window 3 resp. window 4) forces cycle-bijectivity on
  every cycle length simultaneously — this is the engine used everywhere else;
* closure properties: post-composition with a permutation of the alphabet, and
  spatial reflection, preserve cycle-bijectivity;
* `cycleBijective_of_singleCoordinatePerm`: the "trivial" rules
  `g = σ ∘ (one coordinate)` are cycle-bijective (the *easy* half of the
  classification claim under test);
* `diag_bijective_of_cycleBijective`: a first necessary condition.

The hard half of the classification claim (that these are the *only*
cycle-bijective rules) is **false**; see `Cryptography.TernaryReversible.Refutation`.
-/

open Cryptography
open TernaryReversible







/-! ## Coordinate dependence -/






instance : DecidablePred DependsRight := fun g => by unfold DependsRight; infer_instance


/-! ## Local decoders force bijectivity on all cycles -/





/-! ## Closure properties -/




/-! ## The easy half of the classification claim -/


/-! ## A necessary condition -/



open Cryptography.TernaryReversible in
theorem solution{g : LocalRule}
    (h : (DependsLeft g ∧ DependsMiddle g) ∨ (DependsLeft g ∧ DependsRight g) ∨
      (DependsMiddle g ∧ DependsRight g)) : ¬ SingleCoordinatePerm g := by
  rintro ⟨σ, rfl | rfl | rfl⟩
  · have hm : ¬ DependsMiddle (fun (a : Alph) (_ _ : Alph) => σ a) := by
      rintro ⟨a, b, b', c, hne⟩; exact hne rfl
    have hr : ¬ DependsRight (fun (a : Alph) (_ _ : Alph) => σ a) := by
      rintro ⟨a, b, c, c', hne⟩; exact hne rfl
    rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hm h2
    · exact hr h2
    · exact hm h1
  · have hl : ¬ DependsLeft (fun (_ : Alph) (b : Alph) (_ : Alph) => σ b) := by
      rintro ⟨a, a', b, c, hne⟩; exact hne rfl
    have hr : ¬ DependsRight (fun (_ : Alph) (b : Alph) (_ : Alph) => σ b) := by
      rintro ⟨a, b, c, c', hne⟩; exact hne rfl
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hl h1
    · exact hl h1
    · exact hr h2
  · have hl : ¬ DependsLeft (fun (_ _ : Alph) (c : Alph) => σ c) := by
      rintro ⟨a, a', b, c, hne⟩; exact hne rfl
    have hm : ¬ DependsMiddle (fun (_ _ : Alph) (c : Alph) => σ c) := by
      rintro ⟨a, b, b', c, hne⟩; exact hne rfl
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hl h1
    · exact hl h1
    · exact hm h1
