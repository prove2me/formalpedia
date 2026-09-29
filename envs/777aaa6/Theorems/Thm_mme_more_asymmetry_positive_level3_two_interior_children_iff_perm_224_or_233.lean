-- Prove2me | Theorems.Thm_mme_more_asymmetry_positive_level3_two_interior_children_iff_perm_224_or_233
-- name    : mme_more_asymmetry_positive_level3_two_interior_children_iff_perm_224_or_233
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T10:16:29.422678+00:00
-- url     : https://prove2.me/theorems/0c532eae-06ec-413d-8a08-f42a4f407e8a
-- title:
--   Two positive 112 children occur only in shapes 224 or 233 (imported interface)
-- statement:
--   A level-three shape is the coordinatewise sum of two positive level-two 112 shapes exactly when it is a permutation of (2,2,4) or (2,3,3). The theorem imports the shared finite shape predicates rather than placing local definitions in its preamble.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions 3.5–3.6 and Theorem 6.4, pp. 14–15 and 28–31.

import Definitions.Def_mme_more_asymmetry_shape_predicates

set_option autoImplicit false

theorem mme_more_asymmetry_positive_level3_two_interior_children_iff_perm_224_or_233
    (i j k : ℕ) :
    (∃ a₁ b₁ c₁ a₂ b₂ c₂ : ℕ,
      IsPerm112 a₁ b₁ c₁ ∧ IsPerm112 a₂ b₂ c₂ ∧
      a₁ + a₂ = i ∧ b₁ + b₂ = j ∧ c₁ + c₂ = k) ↔
      IsPerm224 i j k ∨ IsPerm233 i j k := by sorry
