-- Prove2me | Theorems.Thm_SolomonZeta_mu_orderIso
-- name    : SolomonZeta.mu_orderIso
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:52:37.028473+00:00
-- url     : https://prove2.me/theorems/8051270b-5a24-4cf0-b811-b6de6fb38787
-- title:
--   The MÃ¶bius function of a locally finite poset is an invariant of the isomorphism type of the
-- statement:
--   The MÃ¶bius function of a locally finite poset is an invariant of the isomorphism type of the
--   poset: order isomorphic intervals have equal MÃ¶bius values.
--
--   ```lean
--   theorem SolomonZeta.mu_orderIso{𝕜 : Type*} [AddCommGroup 𝕜] [One 𝕜] {α β : Type*}
--       [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]
--       [PartialOrder β] [LocallyFiniteOrder β] [DecidableEq β] (e : α ≃o β) (a b : α) :
--       mu 𝕜 (e a) (e b) = mu 𝕜 a b := by sorry
--   /-! ### Coprime splitting of submodule lattices -/
--
--   variable {R M X₁ X₂ : Type*} [Ring R] [AddCommGroup M] [Module R M]
--     [AddCommGroup X₁] [Module R X₁] [AddCommGroup X₂] [Module R X₂]
--
--
--
--
--
--   /-! ### Multiplicativity of the Möbius weight -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/SolomonZeta/Multiplicativity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/SolomonZeta/Multiplicativity.lean#L33

-- Thm stub generated from Shared/SolomonZeta/Multiplicativity.lean
import Mathlib
import Definitions.Def_Shared_SolomonZeta_Core
import Definitions.Def_Shared_SolomonZeta_Multiplicativity
/-
# Euler factorization of the refined Solomon zeta coefficients

The Solomon zeta function of a lattice factors into local Euler factors.  On the level of the
*refined* (Bushnell–Reiner style) coefficients — which record the isomorphism type `X` of the
quotient rather than just its cardinality — this factorization takes the form of a
multiplicativity statement:

  if the finite modules `X₁` and `X₂` are annihilated by coprime integers `a` and `b`, then
  the Möbius weight of `X₁ × X₂` is the product of the Möbius weights of `X₁` and `X₂`,
  and consequently the refined zeta coefficients multiply.

The proof is structural and proceeds in three steps:

1. `SolomonZeta.mu_orderIso` — the Möbius function of a locally finite poset is invariant under
   order isomorphisms (proved by strong induction on the size of the interval);
2. `SolomonZeta.submodule_prod_split` — under coprimality every submodule of `X₁ × X₂` is a
   product of submodules, giving an order isomorphism of submodule lattices
   `SolomonZeta.coprimeSubmoduleOrderIso`;
3. Mathlib's `IncidenceAlgebra.mu_prod_mu` then evaluates the Möbius function of the product
   poset, and the Hom-counts factor because `Hom(M, Y₁ × Y₂) = Hom(M, Y₁) × Hom(M, Y₂)`.
-/

open SolomonZeta

open Finset IncidenceAlgebra


/-! ### Möbius functions are invariant under order isomorphisms -/

theorem SolomonZeta.mu_orderIso{𝕜 : Type*} [AddCommGroup 𝕜] [One 𝕜] {α β : Type*}
    [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]
    [PartialOrder β] [LocallyFiniteOrder β] [DecidableEq β] (e : α ≃o β) (a b : α) :
    mu 𝕜 (e a) (e b) = mu 𝕜 a b := by sorry
