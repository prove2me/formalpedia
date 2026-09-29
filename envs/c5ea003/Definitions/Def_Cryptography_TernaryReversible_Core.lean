-- Prove2me | Definitions.Def_Cryptography_TernaryReversible_Core
-- name    : Cryptography_TernaryReversible_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:23:23.346867+00:00
-- url     : https://prove2.me/theorems/5581600c-5fc7-4a0c-8ac5-6423bd6aef19
-- title:
--   Aether Catalog definitions — Cryptography_TernaryReversible_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.TernaryReversible.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/TernaryReversible/Core.lean by skeleton subtraction
import Mathlib

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

namespace Cryptography
namespace TernaryReversible

/-- The ternary alphabet.  `ZMod 3` *is* `Fin 3` (definitionally, see `Alph_eq_Fin3`);
we use the `ZMod` presentation so that the field structure of `𝔽₃` is available. -/
abbrev Alph := ZMod 3


/-- A radius-one local rule on the ternary alphabet: `g a b c` is the new value of a
cell whose left neighbour is `a`, whose own value is `b` and whose right neighbour
is `c`. -/
abbrev LocalRule := Alph → Alph → Alph → Alph

/-- Global map of a local rule on the cycle `ZMod n` (cyclic boundary conditions). -/
def globalMap (g : LocalRule) {n : ℕ} (s : ZMod n → Alph) : ZMod n → Alph :=
  fun i => g (s (i - 1)) (s i) (s (i + 1))

/-- A rule is *cycle-bijective* when its global map is bijective on every nonempty
finite cycle. -/
def CycleBijective (g : LocalRule) : Prop :=
  ∀ n : ℕ, 0 < n → Function.Bijective (globalMap (n := n) g)

/-- The rules the classification claim predicts: a single coordinate of the window,
post-composed with a permutation of the alphabet. -/
def SingleCoordinatePerm (g : LocalRule) : Prop :=
  ∃ σ : Equiv.Perm Alph,
    g = (fun a _ _ => σ a) ∨ g = (fun _ b _ => σ b) ∨ g = (fun _ _ c => σ c)

/-! ## Coordinate dependence -/

/-- `g` genuinely uses its left argument. -/
def DependsLeft (g : LocalRule) : Prop := ∃ a a' b c, g a b c ≠ g a' b c

/-- `g` genuinely uses its middle argument. -/
def DependsMiddle (g : LocalRule) : Prop := ∃ a b b' c, g a b c ≠ g a b' c

/-- `g` genuinely uses its right argument. -/
def DependsRight (g : LocalRule) : Prop := ∃ a b c c', g a b c ≠ g a b c'

instance : DecidablePred DependsLeft := fun g => by unfold DependsLeft; infer_instance

instance : DecidablePred DependsMiddle := fun g => by unfold DependsMiddle; infer_instance

instance : DecidablePred DependsRight := fun g => by unfold DependsRight; infer_instance


/-! ## Local decoders force bijectivity on all cycles -/





/-! ## Closure properties -/




/-! ## The easy half of the classification claim -/


/-! ## A necessary condition -/


end TernaryReversible
end Cryptography


