-- Prove2me | Theorems.Thm_mme_recursive_joint_parent_type_card
-- name    : mme_recursive_joint_parent_type_card
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T17:30:45.57439+00:00
-- url     : https://prove2.me/theorems/c858e60c-d358-413a-b335-f0b3db337072
-- title:
--   Exact count of the actual joint parent-word type class
-- statement:
--   Compute the parent-type denominator used in the regional Y/Z hash loads as a product of conditional histogram multinomials. The actual parentCounts determine all masses; the two child halves remain joint. No independence or type-count assumption is used.
-- source:
--   Quantitative finite realization for a jointly processed constituent region, connected to the physical recursive Y/Z extraction for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 . This is a supporting lemma, not a proof of the regional asymptotic theorem or a numerical omega certificate.

import Mathlib
import Definitions.Def_mme_recursive_yz_hash_filter



open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem mme_recursive_joint_parent_type_card {half R : ℕ} {n : Fin R → ℕ} {W : Type*} [Fintype W]
    (y : ∀ r, Fin (n r) → Fin (half + 1)) (f : Position n → W) :
    Nat.card {g : Position n → W // ParentType y (parentCounts y f) g} =
      ∏ r, histogramNumber (parentCounts y f r) := by sorry
