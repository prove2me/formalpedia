-- Prove2me | Theorems.Thm_mme_released_positive_region_position_transport
-- name    : mme_released_positive_region_position_transport
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T01:50:29.001216+00:00
-- url     : https://prove2.me/theorems/3e00b541-91ad-4872-8a46-f4ae86ba0b51
-- title:
--   Positive-region positions preserve parent grades and typical bands
-- statement:
--   For every one of the six released regions and every natural-number scale $k$, the 88 compact positive labels admit a position equivalence with the common 270-label system. It preserves each label's parent grade, the occurrence number, and the left or right half. Composing the common position enumeration with this equivalence gives a compact enumeration that splits the same physical fine word into exactly the same child words. The word is parent graded in the compact coordinates if and only if it is parent graded in the common coordinates. For every positive tolerance $\varepsilon$, its compact parent-typical band, formed from $k n_3$, $k m_3$, and $k\mu_3$, is equivalent to the canonical common source predicate. Scale zero is included; no address with a prescribed histogram is assumed or concluded.
-- source:
--   Proposed exact interface transport between the canonical RecStage data and ReleasedJointInterior profiles and positions. The regional decomposition comes from Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/pdf/2404.16349v2, Section 6.1 and Claim 6.5, printed page 32. This transport theorem is not stated verbatim in the paper.

import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_joint_interior_frame
import Definitions.Def_mme_graded_integer_regional_step_data
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open MME.ReleasedJointInterior
set_option autoImplicit false

theorem mme_released_positive_region_position_transport
    (region : Fin 6) (k : ℕ) :
    ∃ (e : Fin 88 ≃ {j : Fin 270 // 0 < size region 1 j})
      (q : Position (fun r => k * RecStage.n3 region r) ≃ Position (size region k)),
      (∀ r, RecStage.parent3 region r = parent region (e r).val) ∧
      (∀ (r : Fin 88) (t : Fin (k * RecStage.n3 region r)) (h : Fin 2),
        (q ⟨r,t,h⟩).1 = (e r).val ∧
        (q ⟨r,t,h⟩).2.1.val = t.val ∧ (q ⟨r,t,h⟩).2.2 = h) ∧
      let compactPositions := (positions region k).trans q.symm
      (∀ (x : ProfiledCW.FineWord (blocks region k * 4))
        (p : Position (fun r => k * RecStage.n3 region r)),
        ProfiledCW.split compactPositions (positions_length region k) x p =
          ProfiledCW.split (positions region k) (positions_length region k) x (q p)) ∧
      (∀ (i : Fin 3) (x : ProfiledCW.FineWord (blocks region k * 4)),
        ParentGraded (RecStage.parent3 region) (fun r => k * RecStage.n3 region r) i
          (ProfiledCW.split compactPositions (positions_length region k) x) ↔
        ParentGraded (parent region) (size region k) i
          (ProfiledCW.split (positions region k) (positions_length region k) x)) ∧
      (∀ (eps : ℝ), 0 < eps →
        ∀ (i : Fin 3) (x : ProfiledCW.FineWord (blocks region k * 4)),
          parentTypical (RecStage.htotal3 region) (fun r => k * RecStage.n3 region r)
            (fun r c => k * RecStage.m3 region r c)
            (fun c w => k * RecStage.mu3 region i c w) eps
            (ProfiledCW.split compactPositions (positions_length region k) x) ↔
          source region k eps i x) := by sorry
