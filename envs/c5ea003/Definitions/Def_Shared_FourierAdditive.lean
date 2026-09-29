-- Prove2me | Definitions.Def_Shared_FourierAdditive
-- name    : Shared_FourierAdditive
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:50:18.722874+00:00
-- url     : https://prove2.me/theorems/3b661376-2015-44a1-8c29-6273ca1cbd69
-- title:
--   Aether Catalog definitions — Shared_FourierAdditive
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.FourierAdditive`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/FourierAdditive.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_FourierFiniteAbelian
/-
# A Fourier-analytic sumset theorem on finite abelian groups

Building on `Catalog.Shared.FourierFiniteAbelian`, this file uses the convolution theorem,
Fourier inversion, Parseval's identity and Cauchy–Schwarz to count representations
`c = a + b` with `a ∈ A`, `b ∈ B` in a finite abelian group `G`.

Main results:

* `FourierAdd.conv_indF` : the convolution of two indicators counts representations.
* `FourierAdd.card_mul_rep_eq` : the Fourier counting formula
  `|G| * r_{A,B}(c) = ∑_ψ ψ(c) · 1̂_A(ψ) · 1̂_B(ψ)`.
* `FourierAdd.norm_error_lt` : the nonprincipal characters contribute strictly less than
  `|A| * |B|` when `(|G| - |A|)(|G| - |B|) < |A||B|`.
* `FourierAdd.exists_add_eq` : consequently `A + B = G`.  The hypothesis turns out to be
  *equivalent* to the pigeonhole bound `|A| + |B| > |G|` (see `cardCondition_iff`), so the
  Fourier/Cauchy–Schwarz route reproduces exactly the pigeonhole threshold — Cauchy–Schwarz is
  tight here.
* `FourierAdd.exists_add_eq_of_card_add_card_gt` : the classical pigeonhole corollary.
* `FourierAdd.cardCondition_iff` : the Cauchy–Schwarz hypothesis is *exactly equivalent* to
  `|A| + |B| > |G|`; so the Fourier route recovers, and does not beat, the pigeonhole threshold.
* `FourierAdd.energy_identity` : the exact Plancherel/additive-energy identity
  `|G| * ∑_c r(c)² = (|A||B|)² + ∑_{ψ ≠ 0} |1̂_A(ψ)|² |1̂_B(ψ)|²`.
* `FourierAdd.card_support_rep_ge` : the resulting quantitative covering bound
  `|{c : r(c) > 0}| ≥ |G| (|A||B|)² / ((|A||B|)² + E)`.
-/


open Finset ComplexConjugate FourierFA

namespace FourierAdd

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The (complex-valued) indicator function of a finset. -/
noncomputable def indF (A : Finset G) : G → ℂ := fun x => if x ∈ A then 1 else 0

/-- The number of representations `c = a + b` with `a ∈ A` and `b ∈ B`. -/
def rep (A B : Finset G) (c : G) : ℕ := (A.filter (fun y => c - y ∈ B)).card















end FourierAdd


