-- Prove2me | Theorems.Thm_sauer_shelah
-- name    : sauer_shelah
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:02:43.506551+00:00
-- url     : https://prove2.me/theorems/6d07fa69-28cd-42e8-bef2-20b2880a13c5
-- title:
--   Sauer–Shelah lemma.
-- statement:
--   **Sauer–Shelah lemma.** A family of subsets of `Fin n` that shatters no set
--   of size greater than `d` contains at most `∑_{i=0}^{d} \binom{n}{i}` members.
--
--   ```lean
--   theorem sauer_shelah: ∀ (n d : ℕ) (F : Finset (Finset (Fin n))),
--       (∀ A, Shatters F A → A.card ≤ d) →
--       F.card ≤ ∑ i ∈ Finset.range (d + 1), n.choose i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/SauerShelah.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/SauerShelah.lean#L222

-- Thm stub generated from Algebra/SauerShelah.lean
import Mathlib
import Definitions.Def_Algebra_SauerShelah

open Fin

/-! # CatalogBuild.Algebra.SauerShelah

Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 17
-/











-- ================================================================
--  Basic proj / embed API
-- ================================================================

theorem sauer_shelah: ∀ (n d : ℕ) (F : Finset (Finset (Fin n))),
    (∀ A, Shatters F A → A.card ≤ d) →
    F.card ≤ ∑ i ∈ Finset.range (d + 1), n.choose i := by sorry
