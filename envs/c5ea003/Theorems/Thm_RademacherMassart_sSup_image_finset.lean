-- Prove2me | Theorems.Thm_RademacherMassart_sSup_image_finset
-- name    : RademacherMassart.sSup_image_finset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:42:05.885354+00:00
-- url     : https://prove2.me/theorems/b4bc03c3-ff4d-4b07-ba43-176a7a738faf
-- title:
--   For a finite class the supremum defining the Rademacher complexity is a maximum.
-- statement:
--   For a finite class the supremum defining the Rademacher complexity is a maximum.
--
--   ```lean
--   theorem RademacherMassart.sSup_image_finset(F : Finset (Fin n → ℝ)) (hne : F.Nonempty) (ε : Fin n → Bool) :
--       sSup (signAvg ε '' (F : Set (Fin n → ℝ))) = (1 / (n : ℝ)) * maxCorr F hne ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Rademacher/Massart.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Rademacher/Massart.lean#L146

-- Thm stub generated from Logic/Rademacher/Massart.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Massart
/-
# Massart's finite class lemma

If a hypothesis class restricted to a sample of size `n` consists of `N` vectors, each
of Euclidean length at most `r`, then its empirical Rademacher complexity is at most

  `r * √(2 log N) / n`.

The proof is the classical Chernoff/MGF argument:

* Jensen's inequality moves the expectation inside the exponential;
* a maximum is bounded by a sum, and the moment generating function of a Rademacher
  sum factorises into hyperbolic cosines, `𝔼 exp(λ⟨σ,v⟩) = ∏ cosh(λ vᵢ)`;
* `cosh t ≤ exp(t²/2)` gives the sub-Gaussian bound `exp(λ²r²/2)`;
* optimising over `λ` yields `√(2 log N)`.

Combined with `Massart` for the class of all `±1` patterns, this shows the bound is
tight up to the absolute constant `√(2 log 2) ≈ 1.177`; see `rad_cube` and
`massart_cube_tight` at the end of the file.

This file is self-contained.
-/

open RademacherMassart

open Finset

variable {n : ℕ}




/-! ### Elementary facts about sign patterns -/





/-! ### The two analytic ingredients -/




/-! ### Massart's lemma -/

theorem RademacherMassart.sSup_image_finset(F : Finset (Fin n → ℝ)) (hne : F.Nonempty) (ε : Fin n → Bool) :
    sSup (signAvg ε '' (F : Set (Fin n → ℝ))) = (1 / (n : ℝ)) * maxCorr F hne ε := by sorry
