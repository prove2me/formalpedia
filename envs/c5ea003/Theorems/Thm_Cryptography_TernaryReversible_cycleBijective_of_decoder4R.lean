-- Prove2me | Theorems.Thm_Cryptography_TernaryReversible_cycleBijective_of_decoder4R
-- name    : Cryptography.TernaryReversible.cycleBijective_of_decoder4R
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:45:31.964818+00:00
-- url     : https://prove2.me/theorems/842c116b-57f7-4a3c-a84b-a9024fb18ca1
-- title:
--   Window-4 (right-looking) decoder criterion.
-- statement:
--   **Window-4 (right-looking) decoder criterion.** If a rule `d` reconstructs the
--   leftmost cell of a window of six from the four outputs it determines, then `g` is
--   bijective on every finite cycle.  Such a decoder is an inverse cellular automaton
--   of neighbourhood `{1,2,3,4}`, i.e. of radius at least two.
--
--   ```lean
--   theorem Cryptography.TernaryReversible.cycleBijective_of_decoder4R(g : LocalRule) (d : Alph → Alph → Alph → Alph → Alph)
--       (h : ∀ x₀ x₁ x₂ x₃ x₄ x₅,
--         d (g x₀ x₁ x₂) (g x₁ x₂ x₃) (g x₂ x₃ x₄) (g x₃ x₄ x₅) = x₀) :
--       CycleBijective g := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/TernaryReversible/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/TernaryReversible/Core.lean#L142

-- Thm stub generated from Cryptography/TernaryReversible/Core.lean
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

theorem Cryptography.TernaryReversible.cycleBijective_of_decoder4R(g : LocalRule) (d : Alph → Alph → Alph → Alph → Alph)
    (h : ∀ x₀ x₁ x₂ x₃ x₄ x₅,
      d (g x₀ x₁ x₂) (g x₁ x₂ x₃) (g x₂ x₃ x₄) (g x₃ x₄ x₅) = x₀) :
    CycleBijective g := by sorry
