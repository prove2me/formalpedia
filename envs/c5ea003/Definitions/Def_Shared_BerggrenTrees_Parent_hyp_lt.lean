-- Prove2me | Definitions.Def_Shared_BerggrenTrees_Parent_hyp_lt
-- name    : Shared_BerggrenTrees_Parent_hyp_lt
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:28.709003+00:00
-- url     : https://prove2.me/theorems/53b6a4ce-9e75-49c4-bf36-75f8ea106785
-- title:
--   Aether Catalog definitions — Shared_BerggrenTrees_Parent_hyp_lt
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.BerggrenTrees.Parent.hyp.lt`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/BerggrenTrees/Parent_hyp_lt.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Parent_hyp_lt

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3

Repaired: the predicate `IsPT` used by the statements was missing from the
catalog and is supplied here (a Pythagorean triple `a² + b² = c²`).  The middle
declaration `parent_exists` is retained verbatim but commented out: it refers to
the Berggren inverse branches `invB1`, `invB2`, `invB3` and to the auxiliary
lemmas `invB1_pos_case`, `invB2_pos_case`, `invB3_pos_case`, `not_both_neg`,
none of which exist anywhere in the catalog, so its statement cannot even be
elaborated.  The two hypotenuse estimates around it are fully proved.
-/

/-- `IsPT a b c` says that `(a, b, c)` is a Pythagorean triple. -/
def IsPT (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2


/- Retained from the catalog but not compilable: `invB1`, `invB2`, `invB3` and the
positivity case lemmas `invB1_pos_case`, `invB2_pos_case`, `invB3_pos_case`,
`not_both_neg` referenced below are not defined anywhere in this development.

/-- [Section: # CatalogBuild.Shared.Parent_hyp_lt
Auto-generated from theorem catalog database.
Domain: Pythagorean/Berggren
Declarations: 3] -/
theorem parent_exists (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hpt : IsPT a b c) (hc5 : c > 5) (hprim : Int.gcd a b = 1) :
    (0 < (invB1 a b c).1 ∧ 0 < (invB1 a b c).2.1 ∧ 0 < (invB1 a b c).2.2) ∨
    (0 < (invB2 a b c).1 ∧ 0 < (invB2 a b c).2.1 ∧ 0 < (invB2 a b c).2.2) ∨
    (0 < (invB3 a b c).1 ∧ 0 < (invB3 a b c).2.1 ∧ 0 < (invB3 a b c).2.2) := by
  by_cases h1 : a + 2 * b = 2 * c;
  · -- If $a + 2b = 2c$, then substituting $c = \frac{a + 2b}{2}$ into $a^2 + b^2 = c^2$ gives $3a^2 = 4ab$, so $3a = 4b$ (since $a > 0$).
    have h_eq : 3 * a = 4 * b := by
      unfold IsPT at hpt; nlinarith;
    -- Since $a$ and $b$ are coprime and $3a = 4b$, it follows that $a = 4k$ and $b = 3k$ for some integer $k$.
    obtain ⟨k, rfl, rfl⟩ : ∃ k : ℤ, a = 4 * k ∧ b = 3 * k := by
      exact ⟨ a / 4, by omega, by omega ⟩;
    simp_all +decide [ Int.gcd_mul_left, Int.gcd_mul_right ];
    grind;
  · by_cases h2 : 2 * a + b = 2 * c;
    · obtain ⟨t, ht⟩ : ∃ t : ℤ, a = 3 * t ∧ b = 4 * t ∧ c = 5 * t := by
        use a / 3;
        have h_eq : 3 * b = 4 * a := by
          nlinarith only [ ha, hb, hc, h2, hpt.symm ];
        omega;
      simp_all +decide [ Int.gcd_mul_left, Int.gcd_mul_right ];
      grind;
    · by_cases h3 : a + 2 * b > 2 * c <;> by_cases h4 : 2 * a + b > 2 * c;
      · exact Or.inr <| Or.inl <| invB2_pos_case a b c ha hb hc hpt h3 h4;
      · exact Or.inl <| invB1_pos_case a b c ha hb hc hpt h3 <| lt_of_le_of_ne ( le_of_not_gt h4 ) h2;
      · exact Or.inr <| Or.inr <| invB3_pos_case a b c ha hb hc hpt ( lt_of_le_of_ne ( le_of_not_gt h3 ) h1 ) h4;
      · exact False.elim <| not_both_neg a b c ha hb hpt ( le_of_not_gt h3 ) ( le_of_not_gt h4 )
-/


