-- Prove2me | solution 1 for Cryptography.TernaryReversible.cycleBijective_comp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:58:11.877658+00:00
-- url     : https://prove2.me/submissions/44206a46-294d-4c8f-a8ea-b76ffdcd2011

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
theorem solution{g : LocalRule} {f : Alph → Alph} (hf : Function.Bijective f)
    (hg : CycleBijective g) : CycleBijective (fun a b c => f (g a b c)) := by
  intro n hn
  have hcomp : globalMap (n := n) (fun a b c => f (g a b c))
      = (fun s => (fun i => f (s i))) ∘ globalMap (n := n) g := rfl
  rw [hcomp]
  refine Function.Bijective.comp ?_ (hg n hn)
  obtain ⟨hinj, hsurj⟩ := hf
  constructor
  · intro s t hst
    funext i
    exact hinj (congrFun hst i)
  · intro t
    choose finv hfinv using hsurj
    exact ⟨fun i => finv (t i), by funext i; simp [hfinv]⟩
