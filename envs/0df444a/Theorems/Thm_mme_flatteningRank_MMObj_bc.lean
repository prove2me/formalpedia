-- Prove2me | Theorems.Thm_mme_flatteningRank_MMObj_bc
-- name    : mme_flatteningRank_MMObj_bc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-02T19:24:04.665884+00:00
-- url     : https://prove2.me/theorems/b368f739-152f-46bc-933c-327029ae4810
-- statement:
--   **Mode-1 flattening rank lower bound for the matrix-multiplication tensor.** The mode-1 flattening rank of $\mathrm{MM}(a, b, c)$ is at least $bc$ whenever $a \ge 1$. Cyclic mode-1 analogue of `mme_flatteningRank_MMObj_ab`. Used in the $\mathrm{BddAbove}$ analysis for $\mathrm{subrankCapacityPoly}$.
-- source:
--   Strassen flattening; cyclic mode-1 of the mode-0 bound

import Definitions.Def_mme_flattening
import Definitions.Def_mme_tensor_rank

namespace MME

/-- The singleton split `S = {1}` of `Fin 3`. -/
noncomputable def split1 : Split (Fin 3) where
  S := {(1 : Fin 3)}
  hS := Finset.singleton_nonempty _
  hSc := by
    refine Finset.nonempty_iff_ne_empty.mpr ?_
    intro h
    have hcard : ({(1 : Fin 3)}ᶜ : Finset (Fin 3)).card = 0 := by rw [h]; rfl
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin] at hcard
    omega

end MME

open MME

universe u

/-- **`b*c ≤ flatteningRank σ_1 (MMObj K a b c)` for `a ≥ 1`.**

Cyclic mode-1 analogue of `mme_flatteningRank_MMObj_ab`. The mode-1 flattening rank of
`MM(a, b, c)` is at least `b*c` whenever `a ≥ 1`. Exposed as a Theorem stub for
downstream use (proof would parallel `Sol_mme_flatteningRank_MMObj_ab.lean` with
cyclic-mode relabelling). -/
theorem mme_flatteningRank_MMObj_bc {K : Type u} [Field K] (a b c : ℕ) (ha : 1 ≤ a) :
    b * c ≤ MME.flatteningRank MME.split1 (MME.MMObj K a b c) := by
  sorry
