-- Prove2me | Theorems.Thm_mme_released_global_physical_orientation
-- name    : mme_released_global_physical_orientation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T15:26:21.099575+00:00
-- url     : https://prove2.me/theorems/1cb17823-5bfc-4f69-9d30-145f5231680b
-- title:
--   Restore the six global regions to physical coordinates
-- statement:
--   Let $r_o$ be the published map from hash coordinates to physical coordinates for orientation $o\in\{0,\ldots,5\}$, and let $h_o$ be the coordinate map used to restore that region. Then
--   $$r_o(h_o(i))=i,\qquad h_o(r_o(i))=i.$$
--   For every global extraction Part $S$, its physical restoration, built from the existing cyclic and transposition constructors, has exactly the same number of input copies and the same logarithmic output rate as $S$. Thus the six distinct numerical rates can be retained while their output predicates are returned to one common system of physical coordinates.
-- source:
--   Auxiliary formalization for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2, Theorem 5.3, Section 5.1, Theorem 6.4 and Algorithm 1. Specialization to the published exact ReleasedGlobal seed; the numerical recursive continuation remains an explicit separate obligation.

import Definitions.Def_mme_released_global_joint_interface
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRealization MME.ReleasedGlobal
set_option autoImplicit false
universe u

theorem mme_released_global_physical_orientation :
    (∀ (o : Fin 6) (i : Fin 3),
      roles o (hashMode o i) = i ∧ hashMode o (roles o i) = i) ∧
    ∀ {M ell : ℕ} {P : Predicate M} (o : Fin 6) (S : Part M ell P),
      (physicalPart o S).inputs = S.inputs ∧
      (physicalPart o S).rate = S.rate := by sorry
