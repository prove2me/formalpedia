-- Prove2me | solution 1 for Cryptography.TernaryReversible.cycleBijective_conj
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:05:48.380125+00:00
-- url     : https://prove2.me/submissions/3d634508-9c32-4169-98ab-96680c799b2d

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
theorem solution{g : LocalRule} (σ : Equiv.Perm Alph) (hg : CycleBijective g) :
    CycleBijective (fun a b c => σ.symm (g (σ a) (σ b) (σ c))) := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hconj : globalMap (n := n) (fun a b c => σ.symm (g (σ a) (σ b) (σ c)))
      = (fun (u : ZMod n → Alph) (i : ZMod n) => σ.symm (u i)) ∘ globalMap (n := n) g ∘
        (fun (u : ZMod n → Alph) (i : ZMod n) => σ (u i)) := rfl
  rw [hconj]
  have hpost : Function.Bijective (fun (u : ZMod n → Alph) (i : ZMod n) => σ.symm (u i)) :=
    ⟨fun u v huv => funext fun i => σ.symm.injective (congrFun huv i),
      fun v => ⟨fun i => σ (v i), by funext i; simp⟩⟩
  have hpre : Function.Bijective (fun (u : ZMod n → Alph) (i : ZMod n) => σ (u i)) :=
    ⟨fun u v huv => funext fun i => σ.injective (congrFun huv i),
      fun v => ⟨fun i => σ.symm (v i), by funext i; simp⟩⟩
  exact hpost.comp ((hg n hn).comp hpre)
