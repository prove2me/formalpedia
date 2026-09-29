-- Prove2me | Theorems.Thm_mme_flatteningRank_MMObj_ca
-- name    : mme_flatteningRank_MMObj_ca
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-02T19:24:18.328465+00:00
-- url     : https://prove2.me/theorems/0f4a27b7-a71c-4615-ba25-eee959c397d6
-- statement:
--   **Mode-2 flattening rank lower bound for the matrix-multiplication tensor.** The mode-2 flattening rank of $\mathrm{MM}(a, b, c)$ is at least $ca$ whenever $b \ge 1$. Cyclic mode-2 analogue of `mme_flatteningRank_MMObj_ab`. Used in the $\mathrm{BddAbove}$ analysis for $\mathrm{subrankCapacityPoly}$.
-- source:
--   Strassen flattening; cyclic mode-2 of the mode-0 bound

import Definitions.Def_mme_flattening
import Definitions.Def_mme_tensor_rank

namespace MME

/-- The singleton split `S = {2}` of `Fin 3`. -/
noncomputable def split2 : Split (Fin 3) where
  S := {(2 : Fin 3)}
  hS := Finset.singleton_nonempty _
  hSc := by
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    intro h
    have hcard : ({(2 : Fin 3)}ᶜ : Finset (Fin 3)).card = 0 := by rw [h]; rfl
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin] at hcard
    omega

end MME

open MME

universe u

/-- **`c*a ≤ flatteningRank σ_2 (MMObj K a b c)` for `b ≥ 1`.**

Cyclic mode-2 analogue of `mme_flatteningRank_MMObj_ab`. The mode-2 flattening rank of
`MM(a, b, c)` is at least `c*a` whenever `b ≥ 1`. Exposed as a Theorem stub for
downstream use. -/
theorem mme_flatteningRank_MMObj_ca {K : Type u} [Field K] (a b c : ℕ) (hb : 1 ≤ b) :
    c * a ≤ MME.flatteningRank MME.split2 (MME.MMObj K a b c) := by
  sorry
