-- Prove2me | Theorems.Thm_descent_step_primitive
-- name    : descent_step_primitive
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:54:45.163472+00:00
-- url     : https://prove2.me/theorems/03ac037b-2a6f-4e7c-81d4-2f60eda56adb
-- title:
--   For any primitive Pythagorean triple with c > 5, there exists a parent step
-- statement:
--   For any primitive Pythagorean triple with c > 5, there exists a parent step
--   producing a positive Pythagorean triple with strictly smaller hypotenuse
--
--   ```lean
--   theorem descent_step_primitive(a b c : ℤ) (h : a^2 + b^2 = c^2)
--       (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hc5 : 5 < c)
--       (hcop : Int.gcd a b = 1) :
--       ∃ (s : BerggrenStep'),
--         let p := parentTriple' s (a, b, c)
--         0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.2.2 < c ∧
--         p.1^2 + p.2.1^2 = p.2.2^2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/NumberTheory/BerggrenDescentComplete.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/NumberTheory/BerggrenDescentComplete.lean#L179

-- Thm stub generated from Speculative/NumberTheory/BerggrenDescentComplete.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_BerggrenDescentComplete

/-! # CatalogBuild.Speculative.BerggrenDescentComplete

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 32
-/

theorem descent_step_primitive(a b c : ℤ) (h : a^2 + b^2 = c^2)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hc5 : 5 < c)
    (hcop : Int.gcd a b = 1) :
    ∃ (s : BerggrenStep'),
      let p := parentTriple' s (a, b, c)
      0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ p.2.2 < c ∧
      p.1^2 + p.2.1^2 = p.2.2^2 := by sorry
