-- Prove2me | solution 1 for Cryptography.TernaryReversible.cycleBijective_of_decoder3
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:58:12.448279+00:00
-- url     : https://prove2.me/submissions/62fdd451-3dbb-4665-ae17-1eaec7f7221f

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

/-- The pointwise decoding identity on a cycle: a window-3 decoder `d` for `g`
reconstructs every cell of a configuration from three consecutive cells of its image,
for every cycle length. -/
theorem decoder3_apply {g d : LocalRule}
    (h : ∀ v w x y z, d (g v w x) (g w x y) (g x y z) = x) {n : ℕ} (u : ZMod n → Alph)
    (i : ZMod n) :
    d (globalMap g u (i - 1)) (globalMap g u i) (globalMap g u (i + 1)) = u i := by
  have e1 : globalMap g u (i - 1) = g (u (i - 1 - 1)) (u (i - 1)) (u i) := by
    simp [globalMap, sub_add_cancel]
  have e3 : globalMap g u (i + 1) = g (u i) (u (i + 1)) (u (i + 1 + 1)) := by
    simp [globalMap, add_sub_cancel_right]
  rw [e1, e3]
  exact h _ _ _ _ _




/-! ## Closure properties -/




/-! ## The easy half of the classification claim -/


/-! ## A necessary condition -/



open Cryptography.TernaryReversible in
theorem solution(g d : LocalRule)
    (h : ∀ v w x y z, d (g v w x) (g w x y) (g x y z) = x) : CycleBijective g := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [← Finite.injective_iff_bijective]
  intro s t hst
  funext i
  rw [← decoder3_apply h s i, ← decoder3_apply h t i, hst]
