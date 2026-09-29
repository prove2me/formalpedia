-- Prove2me | solution 1 for Cryptography.TernaryReversible.diag_bijective_of_cycleBijective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:05:49.901803+00:00
-- url     : https://prove2.me/submissions/6a9ab10c-0cb9-4aa9-bf7d-2914fb66de7b

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
theorem solution{g : LocalRule} (hg : CycleBijective g) :
    Function.Bijective (fun a : Alph => g a a a) := by
  have h1 := hg 1 one_pos
  have e : (fun a : Alph => g a a a)
      = (fun s : ZMod 1 → Alph => s 0) ∘ globalMap (n := 1) g ∘ (fun a _ => a) := by
    funext a
    rfl
  rw [e]
  have hfst : Function.Bijective (fun s : ZMod 1 → Alph => s 0) := by
    constructor
    · intro s t hst
      funext i
      rw [Subsingleton.elim i 0]
      exact hst
    · intro a; exact ⟨fun _ => a, rfl⟩
  have hconst : Function.Bijective (fun (a : Alph) (_ : ZMod 1) => a) := by
    constructor
    · intro a b hab; exact congrFun hab 0
    · intro s; exact ⟨s 0, by funext i; rw [Subsingleton.elim i 0]⟩
  exact hfst.comp (h1.comp hconst)
