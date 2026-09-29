-- Prove2me | solution 1 for Cryptography.TernaryReversible.cycleBijective_reflect
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:05:49.416194+00:00
-- url     : https://prove2.me/submissions/24005c4f-219d-4b56-8ad3-e295d9fa8667

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
    CycleBijective (fun a b c => g c b a) := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hRR : ∀ s : ZMod n → Alph, (fun i : ZMod n => (fun j : ZMod n => s (-j)) (-i)) = s := by
    intro s; funext i; simp
  have hRbij : Function.Bijective (fun (s : ZMod n → Alph) (i : ZMod n) => s (-i)) := by
    constructor
    · intro s t hst
      funext i
      have := congrFun hst (-i)
      simpa using this
    · intro t
      exact ⟨fun i => t (-i), by funext i; simp⟩
  have hconj : globalMap (n := n) (fun a b c => g c b a)
      = (fun (u : ZMod n → Alph) (i : ZMod n) => u (-i)) ∘ globalMap (n := n) g ∘
        (fun (u : ZMod n → Alph) (i : ZMod n) => u (-i)) := by
    funext s i
    show g (s (i + 1)) (s i) (s (i - 1)) = g (s (-(-i - 1))) (s (-(-i))) (s (-(-i + 1)))
    rw [show -(-i - 1) = i + 1 by ring, show -(-i) = i by ring, show -(-i + 1) = i - 1 by ring]
  rw [hconj]
  exact hRbij.comp ((hg n hn).comp hRbij)
