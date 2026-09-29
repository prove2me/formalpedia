-- Prove2me | Theorems.Thm_mme_recursive_yz_count_sigma_fiber
-- name    : mme_recursive_yz_count_sigma_fiber
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:08:17.147186+00:00
-- url     : https://prove2.me/theorems/806e420a-72ee-4206-96cb-d4c2a3c666ce
-- title:
--   Region-labeled cell counts equal their fiber counts
-- statement:
--   A cell whose label records its region counts exactly the positions in that region. The result holds for arbitrary finite dependent position families. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_recursive_yz_compatibility
open MME.RecursiveYZ

theorem mme_recursive_yz_count_sigma_fiber
    {R : Type*} [Fintype R] {P C : R → Type*} [∀ r, Fintype (P r)]
    {W : Type*} (cell : ∀ r, P r → C r) (f : (Σ r, P r) → W)
    (r : R) (c : C r) (w : W) :
    count (fun p : Σ r, P r => (⟨p.1, cell p.1 p.2⟩ : Σ r, C r)) f ⟨r,c⟩ w =
      count (cell r) (fun p => f ⟨r,p⟩) c w := by sorry
