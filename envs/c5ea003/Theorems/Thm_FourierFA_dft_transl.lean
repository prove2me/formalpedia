-- Prove2me | Theorems.Thm_FourierFA_dft_transl
-- name    : FourierFA.dft_transl
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:35:52.449972+00:00
-- url     : https://prove2.me/theorems/b3481bc2-d60e-4810-a685-af4349badbbc
-- title:
--   Translating a function modulates its Fourier transform.
-- statement:
--   Translating a function modulates its Fourier transform.
--
--   ```lean
--   theorem FourierFA.dft_transl(a : G) (f : G → ℂ) (ψ : AddChar G ℂ) :
--       dft (transl a f) ψ = conj (ψ a) * dft f ψ := by sorry
--
--   /-! ## Supports under the symmetries -/
--
--
--
--
--
--
--   /-! ## Extremal functions -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/FourierExtremals.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/FourierExtremals.lean#L38

-- Thm stub generated from Shared/FourierExtremals.lean
import Mathlib
import Definitions.Def_Shared_FourierExtremals
import Definitions.Def_Shared_FourierFiniteAbelian
import Definitions.Def_Shared_FourierSubgroupDuality
/-
# Symmetries of the discrete Fourier transform and extremals of the uncertainty principle

Building on `Catalog.Shared.FourierFiniteAbelian` and `Catalog.Shared.FourierSubgroupDuality`,
this file records how the DFT interacts with the three basic symmetries of `G → ℂ`
(scaling, translation, modulation) and deduces a large family of functions attaining
equality in the Donoho–Stark uncertainty principle `|supp f| * |supp f̂| ≥ |G|`.

Main results:

* `FourierFA.dft_transl` : `(f(· - a))^(ψ) = conj (ψ a) · f̂(ψ)` (translation ↦ modulation).
* `FourierFA.dft_modul` : `(χ · f)^(ψ) = f̂(ψ - χ)` (modulation ↦ translation in the dual).
* `FourierFA.IsExtremal` : the property `|supp f| * |supp f̂| = |G|`.
* `FourierFA.IsExtremal.smul`, `.transl`, `.modul` : the extremal functions form a set invariant
  under the three symmetries.
* `FourierFA.isExtremal_coset_modulation` : every function of the form
  `x ↦ c · χ x · 1_H (x - a)` (with `c ≠ 0`, `H` a subgroup) is extremal.
-/


open Finset ComplexConjugate

open FourierFA

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## The three symmetries -/



omit [DecidableEq G] in

theorem FourierFA.dft_transl(a : G) (f : G → ℂ) (ψ : AddChar G ℂ) :
    dft (transl a f) ψ = conj (ψ a) * dft f ψ := by sorry
