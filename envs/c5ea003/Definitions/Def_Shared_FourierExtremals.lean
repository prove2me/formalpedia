-- Prove2me | Definitions.Def_Shared_FourierExtremals
-- name    : Shared_FourierExtremals
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:50:10.232343+00:00
-- url     : https://prove2.me/theorems/c0f62488-68a1-494f-8c08-56fed2a89ee6
-- title:
--   Aether Catalog definitions — Shared_FourierExtremals
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.FourierExtremals`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/FourierExtremals.lean by skeleton subtraction
import Mathlib
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

namespace FourierFA

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## The three symmetries -/

/-- Translation of a function by `a`. -/
def transl (a : G) (f : G → ℂ) : G → ℂ := fun x => f (x - a)

/-- Modulation of a function by a character. -/
def modul (χ : AddChar G ℂ) (f : G → ℂ) : G → ℂ := fun x => χ x * f x



/-! ## Supports under the symmetries -/






/-! ## Extremal functions -/

/-- A function is *extremal* for the uncertainty principle when `|supp f| * |supp f̂| = |G|`,
the smallest value allowed by `FourierFA.uncertainty`. -/
def IsExtremal (f : G → ℂ) : Prop :=
  (supp f).card * (supp (dft f)).card = Fintype.card G







end FourierFA


