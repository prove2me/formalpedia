-- Prove2me | Theorems.Thm_mme_released_recursive_level3_coarse0
-- name    : mme_released_recursive_level3_coarse0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T06:50:48.157896+00:00
-- url     : https://prove2.me/theorems/ac716726-9ccf-4df8-b41d-65f8a6041dfd
-- title:
--   Coarse entropy floors for the first twenty-three regions of level-three band zero
-- statement:
--   A rational lower bound on the coarse entropy of the first twenty-three regions of the first
--   level-three band.
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

theorem mme_released_recursive_level3_coarse0 :
    ((693147180557621093303788000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (0 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559944616464256000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (1 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559931020083788000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (2 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559903681992448000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (3 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147120551243230191973300339 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (4 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900555786198873215380917355445 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (5 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -7) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -5 else if k.val = 2 then 1 else -5) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911275493466533215811846277514 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (6 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 1) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (26 : Int) else if k.val = 1 then -8 else if k.val = 2 then -8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904148507341222758435583014108 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (7 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908333282906631431659016136114 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (8 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else -7) else if j.val = 1 then (if k.val = 0 then (35 : Int) else if k.val = 1 then -1 else if k.val = 2 then -5 else -8) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 5 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809626625429746788228623425964 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (9 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else 0) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 5 else if k.val = 2 then -7 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812612010370956283422246643728 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (10 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -3 else if k.val = 2 then 6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809368863690079037868063431970 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (11 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 3) else if j.val = 1 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else -1) else if j.val = 3 then (if k.val = 0 then (-10 : Int) else if k.val = 1 then -3 else if k.val = 2 then 0 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811731266303261404836863156328 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (12 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -8) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (19 : Int) else if k.val = 1 then 7 else if k.val = 2 then -6 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((555854756950930254444435106629 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (13 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-8 : Int) else if k.val = 1 then -7 else if k.val = 2 then -4 else 6) else if j.val = 1 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then 0 else -3) else if j.val = 3 then (if k.val = 0 then (-26 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 4 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then 0 else if k.val = 2 then -8 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((769479411425482186167721897559 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (14 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 0) else if j.val = 2 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 4 else if k.val = 2 then 7 else -2) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -7 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((711976104258674641619546421463 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (15 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else if j.val = 3 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 0 else if k.val = 2 then 5 else 0) else if j.val = 4 then (if k.val = 0 then (4 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559619816346832000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (16 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945134913132000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (17 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559939087993856000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (18 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693146883226389673391137512447 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (19 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-11 : Int) else if k.val = 1 then -2 else if k.val = 2 then -4 else 8) else if j.val = 1 then (if k.val = 0 then (9 : Int) else if k.val = 1 then 2 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908848576901332390516255259746 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (20 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else if j.val = 1 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then 3 else if k.val = 2 then -7 else 6) else if j.val = 2 then (if k.val = 0 then (-7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 5 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911395109752143863924554664810 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (21 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904134294053043176435190090736 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 0) 0 (22 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) := by sorry
