-- Prove2me | solution 1 for P2M_Basis_ntwist__toSubmodule_le_ntwist__toSubmodule_dea830e69c76
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:24:06.262104+00:00
-- url     : https://prove2.me/submissions/4dc4f3fe-18e2-4dab-91f2-4b6b4b79b73a

import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_ValuationRings
import Definitions.Def_BruhatTits_Lattice_Construction
import Theorems.Thm_P2M_Basis_ntwist__le_ntwist__iff_9a842b8436ac

set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Basis
variable {ι : Type*}
variable [Fintype ι]
open Pointwise
namespace Basis
theorem _root_.solution (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R}
    (hϖ : Irreducible ϖ) {n₁ m₁ n₂ m₂ : ℕ} (hn : n₂ ≤ n₁) (hm : m₂ ≤ m₁) :
    (b.ntwist₂ hϖ n₁ m₁).toSubmodule (R := R) ≤ (b.ntwist₂ hϖ n₂ m₂).toSubmodule (R := R) := by
  rw [ntwist₂_le_ntwist₂_iff]
  exact ⟨hn, hm⟩
end Basis
