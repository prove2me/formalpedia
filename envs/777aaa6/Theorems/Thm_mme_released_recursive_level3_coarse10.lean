-- Prove2me | Theorems.Thm_mme_released_recursive_level3_coarse10
-- name    : mme_released_recursive_level3_coarse10
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T10:38:06.597741+00:00
-- url     : https://prove2.me/theorems/c5a615c5-3dbe-4a55-b6b6-f8f017fb3165
-- title:
--   Coarse entropy floors for regions 44 to 87 of level-three band 4
-- statement:
--   A rational lower bound on the coarse entropy of regions 44 to 87 of level-three
--   band 4.
--
--   For each region the bound is the floor that a table of small-prime references assigns to the
--   region's normalised grade distribution: the total mass the references leave unexplained, corrected
--   by certified enclosures for the logarithms of two, three, five and seven.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_floor_data
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem mme_released_recursive_level3_coarse10 :
    ((768127764301229741304997858058 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (44 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else if j.val = 2 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 3 then (if k.val = 0 then (25 : Int) else if k.val = 1 then 3 else if k.val = 2 then -6 else -6) else if j.val = 4 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 2 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((814051919860347967453034530207 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (45 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 3 then (if k.val = 0 then (-29 : Int) else if k.val = 1 then -8 else if k.val = 2 then 8 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((913523074985922241635849950810 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (46 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147176320240717253036000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (47 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((541180737380624197153392581904 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (48 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 0) else if j.val = 4 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811877301077083471639443609560 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (49 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180557850018427088000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (50 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808497084789076486700589988053 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (51 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 0) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then 1 else if k.val = 2 then -6 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945169515648000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (52 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809606773586689517385998719850 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (53 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -3) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904101392715791484866693310392 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (54 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -1) else if j.val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900199270264291755529499818451 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (55 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -1) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147035098486360120508801025 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (56 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((711920765226528674414692795685 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (57 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((769499588009452763230169921478 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (58 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else -8) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -1 else if k.val = 2 then -6 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809613051837585436886761574279 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (59 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -3) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900553977589347009069508420834 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (60 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -7) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693146832004325337769191326700 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (61 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((555861117124767761723585701433 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (62 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812598407739909718941214269880 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (63 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 3) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -7 else if k.val = 2 then -5 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911273294943225870210586493818 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (64 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559934353608332000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (65 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809334046260627355902765110426 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (66 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (-5 : Int) else if k.val = 1 then -2 else if k.val = 2 then 2 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559943320614016000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (67 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811730108517287143723935714060 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (68 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904173537277117988515101760103 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (69 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908308807483168200389391263148 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (70 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 4) else if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -3 else if k.val = 2 then -6 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945176706832000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (71 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945229850832000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (72 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((712047937852289715885666312985 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (73 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 3) else if j.val = 3 then (if k.val = 0 then (36 : Int) else if k.val = 1 then 0 else if k.val = 2 then -6 else -8) else if j.val = 4 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((769485884848233496374812645712 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (74 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812699318882261418586821284031 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (75 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 3) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 1 else if k.val = 2 then -4 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908834842071177326249467244559 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (76 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 6) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147126156656193543936308395 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (77 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else 1) else if j.val = 1 then (if k.val = 0 then (0 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((555860243632069264890026838967 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (78 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then 4 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812616744654764801123986716370 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (79 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -5) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 3 else if k.val = 2 then 0 else -5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911391161240935185140221050852 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (80 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945024280236000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (81 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809263012016830707453111634956 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (82 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (1 : Int) else if k.val = 1 then 6 else if k.val = 2 then 0 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945273176832000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (83 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((810301755187771029935204828691 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (84 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else -6) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 2 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 6 else if k.val = 2 then -6 else -2) else if j.val = 3 then (if k.val = 0 then (12 : Int) else if k.val = 1 then 2 else if k.val = 2 then -2 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904069347799499958805262237154 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (85 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else if j.val = 1 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -1 else if k.val = 2 then -7 else -1) else if j.val = 2 then (if k.val = 0 then (20 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900150591845555583510334824602 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (86 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 0 else if k.val = 2 then -7 else 2) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 4 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147033294038099932950429760 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 4) 0 (87 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -5 else if k.val = 2 then 8 else -7) else if j.val = 1 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) := by sorry
