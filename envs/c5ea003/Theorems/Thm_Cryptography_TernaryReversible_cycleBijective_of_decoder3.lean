-- Prove2me | Theorems.Thm_Cryptography_TernaryReversible_cycleBijective_of_decoder3
-- name    : Cryptography.TernaryReversible.cycleBijective_of_decoder3
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:44:47.31106+00:00
-- url     : https://prove2.me/theorems/69f45fc3-6dcd-46c7-a1a1-b38ced2f1712
-- title:
--   Window-3 decoder criterion.
-- statement:
--   **Window-3 decoder criterion.** If a local rule `d` reconstructs the middle cell
--   from three consecutive output cells, then `g` is bijective on every finite cycle.
--   Note the decoder identity is a statement about *words*, yet it yields bijectivity
--   for *all* cycle lengths at once, including lengths shorter than the window.
--
--   ```lean
--   theorem Cryptography.TernaryReversible.cycleBijective_of_decoder3(g d : LocalRule)
--       (h : ∀ v w x y z, d (g v w x) (g w x y) (g x y z) = x) : CycleBijective g := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/TernaryReversible/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/TernaryReversible/Core.lean#L122

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

theorem Cryptography.TernaryReversible.cycleBijective_of_decoder3(g d : LocalRule)
    (h : ∀ v w x y z, d (g v w x) (g w x y) (g x y z) = x) : CycleBijective g := by sorry
