-- Prove2me | Theorems.Thm_mme_regional_child_profile_nonempty_iff_support
-- name    : mme_regional_child_profile_nonempty_iff_support
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:31:33.024764+00:00
-- url     : https://prove2.me/theorems/e08128ac-27c8-4871-8d99-6925cf0d0c5a
-- title:
--   Regional child profiles are realizable exactly when their grades agree
-- statement:
--   Fix a physical reference assignment with exact split counts $m_r(c)$, and child-word multiplicities $\mu(c,w)$ satisfying
--   $$\sum_w\mu(c,w)=m_r(c)+m_r(\bar c),$$
--   where $\bar c$ is the complementary split. There exists a word assignment to the physical child positions with exactly this profile and the specified cell grades if and only if every word with positive multiplicity has its cell grade. Both occurrences of each complementary pair are counted.
-- source:
--   Physical complementary cells and released (1,1,6) integer profile mass and support.

import Theorems.Thm_mme_recursive_cellWord_nonempty_iff_mass_and_grade

open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false

theorem mme_regional_child_profile_nonempty_iff_support
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    {W G : Type*} [Fintype W]
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m)
    (grade : W → G) (shape : Cell half R parent → G)
    (mu : Cell half R parent → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2 +
      m c.1 (complement (htotal c.1) c.2)) :
    Nonempty (CellWord (fullCell htotal a) grade shape mu) ↔
      ∀ c w, 0 < mu c w → grade w = shape c := by sorry
