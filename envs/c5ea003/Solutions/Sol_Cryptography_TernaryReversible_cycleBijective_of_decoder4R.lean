-- Prove2me | solution 1 for Cryptography.TernaryReversible.cycleBijective_of_decoder4R
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:05:48.867974+00:00
-- url     : https://prove2.me/submissions/d3258540-f3ca-41df-8f18-d991184c399b

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
theorem solution(g : LocalRule) (d : Alph → Alph → Alph → Alph → Alph)
    (h : ∀ x₀ x₁ x₂ x₃ x₄ x₅,
      d (g x₀ x₁ x₂) (g x₁ x₂ x₃) (g x₂ x₃ x₄) (g x₃ x₄ x₅) = x₀) :
    CycleBijective g := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [← Finite.injective_iff_bijective]
  intro s t hst
  funext i
  have key : ∀ u : ZMod n → Alph,
      d (globalMap g u (i + 1)) (globalMap g u (i + 2)) (globalMap g u (i + 3))
        (globalMap g u (i + 4)) = u i := by
    intro u
    have e : ∀ k : ZMod n,
        globalMap g u (k + 1) = g (u k) (u (k + 1)) (u (k + 2)) := by
      intro k
      have h1 : k + 1 - 1 = k := by ring
      have h2 : k + 1 + 1 = k + 2 := by ring
      simp only [globalMap, h1, h2]
    have e1 := e i
    have e2 : globalMap g u (i + 2) = g (u (i + 1)) (u (i + 2)) (u (i + 3)) := by
      have := e (i + 1)
      rw [show i + 1 + 1 = i + 2 by ring, show i + 1 + 2 = i + 3 by ring] at this
      exact this
    have e3 : globalMap g u (i + 3) = g (u (i + 2)) (u (i + 3)) (u (i + 4)) := by
      have := e (i + 2)
      rw [show i + 2 + 1 = i + 3 by ring, show i + 2 + 2 = i + 4 by ring] at this
      exact this
    have e4 : globalMap g u (i + 4) = g (u (i + 3)) (u (i + 4)) (u (i + 5)) := by
      have := e (i + 3)
      rw [show i + 3 + 1 = i + 4 by ring, show i + 3 + 2 = i + 5 by ring] at this
      exact this
    rw [e1, e2, e3, e4]
    exact h _ _ _ _ _ _
  rw [← key s, ← key t, hst]
