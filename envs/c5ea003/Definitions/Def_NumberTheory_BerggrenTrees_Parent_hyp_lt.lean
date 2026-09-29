-- Prove2me | Definitions.Def_NumberTheory_BerggrenTrees_Parent_hyp_lt
-- name    : NumberTheory_BerggrenTrees_Parent_hyp_lt
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:41.685833+00:00
-- url     : https://prove2.me/theorems/87b40904-b60f-4f3b-b9dc-741ed36367ac
-- title:
--   Aether Catalog definitions — NumberTheory_BerggrenTrees_Parent_hyp_lt
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.BerggrenTrees.Parent.hyp.lt`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/BerggrenTrees/Parent_hyp_lt.lean by skeleton subtraction
import Mathlib

/-- A Pythagorean triple over the integers (supplied here: the catalog module that originally
provided it is not part of this repository). -/
def IsPT (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

/-! # CatalogBuild.Shared.Parent_hyp_lt

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/


-- The theorem `parent_exists` below is disabled: it refers to the Berggren inverse maps
-- `invB1`, `invB2`, `invB3` and to the auxiliary lemmas `invB1_pos_case`, `invB2_pos_case`,
-- `invB3_pos_case`, `not_both_neg`, none of which are part of this repository, so the statement
-- cannot even be elaborated here.  The original text is preserved verbatim below.
-- /-- [Section: # CatalogBuild.Shared.Parent_hyp_lt
-- Auto-generated from theorem catalog database.
-- Domain: Pythagorean/Berggren
-- Declarations: 3] -/
-- theorem parent_exists (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
--     (hpt : IsPT a b c) (hc5 : c > 5) (hprim : Int.gcd a b = 1) :
--     (0 < (invB1 a b c).1 ∧ 0 < (invB1 a b c).2.1 ∧ 0 < (invB1 a b c).2.2) ∨
--     (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) ∨
--     (0 < (invB3 a b c).1 ∧ 0 < (invB3 a b c).2.1 ∧ 0 < (invB3 a b c).2.2) := by
--   by_cases h1 : a + 2 * b = 2 * c;
--   · -- If $a + 2b = 2c$, then substituting $c = \frac{a + 2b}{2}$ into $a^2 + b^2 = c^2$ gives $3a^2 = 4ab$, so $3a = 4b$ (since $a > 0$).
--     have h_eq : 3 * a = 4 * b := by
--       unfold IsPT at hpt; nlinarith;
--     -- Since $a$ and $b$ are coprime and $3a = 4b$, it follows that $a = 4k$ and $b = 3k$ for some integer $k$.
--     obtain ⟨k, rfl, rfl⟩ : ∃ k : ℤ, a = 4 * k ∧ b = 3 * k := by
--       exact ⟨ a / 4, by omega, by omega ⟩;
--     simp_all +decide [ Int.gcd_mul_left, Int.gcd_mul_right ];
--     grind;
--   · by_cases h2 : 2 * a + b = 2 * c;
--     · -- If $2a + b = 2c$, then substituting $c = (2a + b)/2$ into $a^2 + b^2 = c^2$ gives $3b^2 = 4ab$, so $3b = 4a$ (b>0). So $a = 3t$, $b = 4t$, $c = 5t$. Primitivity (gcd(a,b)=1) forces $t=1$, so $c=5$, contradicting $c > 5$.
--       obtain ⟨t, ht⟩ : ∃ t : ℤ, a = 3 * t ∧ b = 4 * t ∧ c = 5 * t := by
--         use a / 3;
--         have h_eq : 3 * b = 4 * a := by
--           nlinarith only [ ha, hb, hc, h2, hpt.symm ];
--         omega;
--       simp_all +decide [ Int.gcd_mul_left, Int.gcd_mul_right ];
--       grind;
--     · by_cases h3 : a + 2 * b > 2 * c <;> by_cases h4 : 2 * a + b > 2 * c;
--       · exact Or.inr <| Or.inl <| invB2_pos_case a b c ha hb hc hpt h3 h4;
--       · exact Or.inl <| invB1_pos_case a b c ha hb hc hpt h3 <| lt_of_le_of_ne ( le_of_not_gt h4 ) h2;
--       · exact Or.inr <| Or.inr <| invB3_pos_case a b c ha hb hc hpt ( lt_of_le_of_ne ( le_of_not_gt h3 ) h1 ) h4;
--       · exact False.elim <| not_both_neg a b c ha hb hpt ( le_of_not_gt h3 ) ( le_of_not_gt h4 )


