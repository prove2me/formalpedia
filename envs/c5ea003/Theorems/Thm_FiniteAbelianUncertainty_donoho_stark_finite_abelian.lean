-- Prove2me | Theorems.Thm_FiniteAbelianUncertainty_donoho_stark_finite_abelian
-- name    : FiniteAbelianUncertainty.donoho_stark_finite_abelian
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:47:28.672857+00:00
-- url     : https://prove2.me/theorems/b000fbca-fd7b-4664-b731-327fffa274dd
-- title:
--   The Donoho–Stark uncertainty principle for an arbitrary finite abelian group.
-- statement:
--   **The Donoho–Stark uncertainty principle for an arbitrary finite abelian group.** A nonzero
--   function and its Fourier transform on the Pontryagin dual cannot both be concentrated:
--   `|G| ≤ |supp f| * |supp 𝓖f|`.
--
--   ```lean
--   theorem FiniteAbelianUncertainty.donoho_stark_finite_abelian(f : G → ℂ) (hf : f ≠ 0) :
--       Fintype.card G ≤ (gsupport f).card * (dsupport (gdft f)).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/FiniteAbelianUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/FiniteAbelianUncertainty.lean#L104

-- Thm stub generated from Bridges/FiniteAbelianUncertainty.lean
import Mathlib
import Definitions.Def_Bridges_FiniteAbelianUncertainty
import Definitions.Def_Bridges_FourierFunctorUncertainty

/-!
# Donoho–Stark uncertainty for arbitrary finite abelian groups

`Catalog/Bridges/FourierFunctorUncertainty.lean` proved the Donoho–Stark uncertainty principle on
`ZMod N`, where the characters are explicit roots of unity. This file shows the argument is
structural rather than cyclic: it needs only that characters have modulus one and that the
character-sum inversion formula holds. We therefore obtain the uncertainty principle for an
arbitrary finite abelian group `G`, with the Fourier transform taking values on the Pontryagin
dual `AddChar G ℂ`.

## Main results

* `FiniteAbelianUncertainty.gdft_inversion` : the character-sum inversion formula
  `∑_ψ ψ b · 𝓖f(ψ) = |G| · f b`.
* `FiniteAbelianUncertainty.donoho_stark_finite_abelian` : for every nonzero `f : G → ℂ`,
  `|G| ≤ |supp f| * |supp 𝓖f|`, the support on the right being taken in the dual group.
* `FiniteAbelianUncertainty.donoho_stark_sharp_delta` : the bound is attained by delta functions,
  so it is sharp for every finite abelian group.
-/

open Finset AddChar

open FiniteAbelianUncertainty

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem FiniteAbelianUncertainty.donoho_stark_finite_abelian(f : G → ℂ) (hf : f ≠ 0) :
    Fintype.card G ≤ (gsupport f).card * (dsupport (gdft f)).card := by sorry
