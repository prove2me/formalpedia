-- Prove2me | Theorems.Thm_mme_entropy_regional_boundary_match_level_two
-- name    : mme_entropy_regional_boundary_match_level_two
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-15T19:19:00.01653+00:00
-- url     : https://prove2.me/theorems/ed4b15ed-da0d-4f1c-be1e-121818692297
-- title:
--   Level-two boundary match from profile data and alignment
-- statement:
--   Level-two boundary-match packaging lemma. Given an integer entropy step $S$ at level $2$, a level-two boundary profile $prof$ of dimension $25$, and a proof that the profile grade and usefulness conditions imply the step output, there is boundary data $B$ over the step output with matrix dimensions multiplying to $25$. The construction packs the profile into a single-cell, single-part boundary end; the alignment hypothesis becomes exactly the required inside proof, and the dimension identity is the profile dimension. This separates routine packaging (proved once, here as the accompanying proof) from the analytic copy bound and the profile alignment, which remain open. **Formalization Note** Lean fixes canonical conventions ($L=1$, one cell, profile mode $0$); the dimension product collapses to the profile dimension.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6, Section 6 regional entropy construction with the level-two profile on the word (1,1) giving 5^2=25 dimensions

import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_recursive_yz_boundary_data
import Definitions.Def_mme_recursive_yz_CW_cells
import Definitions.Def_mme_recursive_yz_compatibility
import Definitions.Def_mme_recursive_yz_cell_partition

set_option autoImplicit false

theorem mme_entropy_regional_boundary_match_level_two
    (S : MME.RegionRealization.IntegerStep 2 2 (fun _ _ => True))
    (prof : MME.RecursiveYZ.Boundary.Profile 2 1)
    (hDim : prof.dim = 25)
    (halign : (forall (i : Fin 3) (x : MME.ProfiledCW.FineWord 2),
        ((forall _p : Fin 1,
            MME.RecursiveYZ.CWCells.grade
              (@MME.ProfiledCW.split (Fin 1) 2 1 2 (Equiv.refl (Fin 1))
                (by decide : 1 * 2 ^ (2 - 1) = 2) x _p) =
              (prof.shape 0) i) /\
          MME.RecursiveYZ.Useful (fun _ : Fin 1 => (0 : Fin 1))
            (fun _ : Fin 1 => prof.mu 0 i)
            (@MME.ProfiledCW.split (Fin 1) 2 1 2 (Equiv.refl (Fin 1))
              (by decide : 1 * 2 ^ (2 - 1) = 2) x)) ->
        S.output i x)) :
    exists (B : MME.ProfiledCW.BoundaryEnd 2 2 S.output),
      B.a * B.b * B.c = 25 /\ Nat.le 1 (B.a * B.b * B.c) := by sorry
