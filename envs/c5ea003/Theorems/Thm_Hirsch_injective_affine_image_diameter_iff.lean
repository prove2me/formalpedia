-- Prove2me | Theorems.Thm_Hirsch_injective_affine_image_diameter_iff
-- name    : Hirsch.injective_affine_image_diameter_iff
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T14:51:21.578084+00:00
-- url     : https://prove2.me/theorems/c4b0c852-981b-4bd7-8578-07e72315c3c9
-- title:
--   Injective affine embeddings preserve vertex-edge diameter
-- statement:
--   Let E and F be real vector spaces, let f:E→F be an injective affine map, let P be any subset of E, and let B be a natural number. The vertex-edge graph of f(P) has padded diameter at most B if and only if the vertex-edge graph of P does. Adjacency means that the distinct endpoints span an extreme segment in the set. No surjectivity onto F, equal ambient dimensions, convexity, boundedness, nonemptiness, or positive B is assumed.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/be54654435d3c317d676f3ea03c79d07f089992a ; standalone Lean/Axiom gate Actions run 34611873550

import Mathlib
import Definitions.Def_Hirsch_model
open Set

namespace Hirsch
theorem injective_affine_image_diameter_iff
    {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    (P : Set E) (B : ℕ) :
    Hirsch.DiamLE (f '' P) B ↔ Hirsch.DiamLE P B := by sorry
end Hirsch
