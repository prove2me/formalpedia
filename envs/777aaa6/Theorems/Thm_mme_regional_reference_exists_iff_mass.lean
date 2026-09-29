-- Prove2me | Theorems.Thm_mme_regional_reference_exists_iff_mass
-- name    : mme_regional_reference_exists_iff_mass
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:29:43.377753+00:00
-- url     : https://prove2.me/theorems/e5d50c04-3c4b-4414-8ae8-41937a4abe60
-- title:
--   Regional reference assignments exist exactly when split mass matches size
-- statement:
--   For each region $r$, let $n_r$ be its number of positions and let $m_r(c)$ be the prescribed nonnegative integer multiplicity of each admissible left-half split $c$. There exists an assignment $a_r$ of splits to positions, simultaneously in all regions, with these exact multiplicities if and only if
--   $$\sum_c m_r(c)=n_r\qquad\text{for every region }r.$$
--   This characterizes when the exact target family contains a physical reference assignment. Empty regions are allowed.
-- source:
--   Recursive exact split-count target families and released (1,1,6) integer regional profiles.

import Definitions.Def_mme_recursive_x_hash_families
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma

open BigOperators MME MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical
set_option autoImplicit false

theorem mme_regional_reference_exists_iff_mass
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) :
    (∃ a : Address half R parent n, a ∈ target m) ↔
      ∀ r, ∑ c, m r c = n r := by sorry
