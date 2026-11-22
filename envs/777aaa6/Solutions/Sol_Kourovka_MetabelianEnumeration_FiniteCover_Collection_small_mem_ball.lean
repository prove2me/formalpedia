-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.small_mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:54:45.958399+00:00
-- url     : https://prove2.me/submissions/cbee88c3-b3de-49d2-a0ab-b9d212c3ed0c

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (u : Lattice k) (ρ : ℝ)
    (hρ : 2 * (k : ℝ) < ρ) (hu : ‖euclidean u‖ ≤ ρ / (2 * k)) : u ∈ ball ρ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < 2 * k := by linarith
  have hρ0 : 0 < ρ := by linarith
  exact hu.trans_lt ((div_lt_iff₀ hk0).mpr (by nlinarith))
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
