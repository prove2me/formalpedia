-- Prove2me | Theorems.Thm_mme_released_recursive_level3_coarse11
-- name    : mme_released_recursive_level3_coarse11
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T10:43:16.161284+00:00
-- url     : https://prove2.me/theorems/f41f206c-e887-4a75-aadb-4224b70e962e
-- title:
--   Coarse entropy floors for regions 0 to 43 of level-three band 5
-- statement:
--   A rational lower bound on the coarse entropy of regions 0 to 43 of level-three
--   band 5.
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

theorem mme_released_recursive_level3_coarse11 :
    ((695666071826021116280564508112 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (0 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (47 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((810515002463664360995393992159 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (1 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 6) else if j.val = 1 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 2 then (if k.val = 0 then (13 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else -5) else if j.val = 3 then (if k.val = 0 then (-18 : Int) else if k.val = 1 then 7 else if k.val = 2 then -7 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((908502947935363354928522142625 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (2 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 6 else if k.val = 2 then 2 else -1) else if j.val = 2 then (if k.val = 0 then (0 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147105845417780465023383110 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (3 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-6 : Int) else if k.val = 1 then -1 else if k.val = 2 then -2 else 4) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 1 else if k.val = 2 then 2 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808121269446128009187287469177 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (4 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 2) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 3 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -8 else if k.val = 2 then -4 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904325616033699840221917313855 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (5 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -2) else if j.val = 1 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else 3) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then 3 else if k.val = 2 then -5 else -2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559900619457232000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (6 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811387260541613574433574255248 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (7 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else 6) else if j.val = 1 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 2 then (if k.val = 0 then (-34 : Int) else if k.val = 1 then 7 else if k.val = 2 then 7 else 2) else if j.val = 3 then (if k.val = 0 then (-30 : Int) else if k.val = 1 then -3 else if k.val = 2 then 5 else 6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((813667001534623803545524601408 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (8 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -8) else if j.val = 1 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 2 then (if k.val = 0 then (-24 : Int) else if k.val = 1 then -2 else if k.val = 2 then 4 else 6) else if j.val = 3 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559944823920076000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (9 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((913641357128427516315373139679 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (10 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else if j.val = 1 then (if k.val = 0 then (19 : Int) else if k.val = 1 then -6 else if k.val = 2 then -8 else 3) else if j.val = 2 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -4 else if k.val = 2 then 1 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945280580332000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (11 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945290057232000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (12 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((705297491018475363293517808845 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (13 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((809570904621405270276514331153 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (14 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 0 else if k.val = 2 then 1 else -7) else if j.val = 1 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 2 then (if k.val = 0 then (12 : Int) else if k.val = 1 then -7 else if k.val = 2 then 4 else -4) else if j.val = 3 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 0 else if k.val = 2 then 1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((900203956605378915741441476193 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (15 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then -6 else if k.val = 2 then -1 else -1) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 6 else if k.val = 2 then -2 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693146760684626987093523477428 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (16 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 2 else if k.val = 2 then 7 else -3) else if j.val = 1 then (if k.val = 0 then (10 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else 3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((768086878270588868170666870668 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (17 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -1) else if j.val = 2 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 2) else if j.val = 3 then (if k.val = 0 then (-23 : Int) else if k.val = 1 then 3 else if k.val = 2 then 5 else 2) else if j.val = 4 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 8 else if k.val = 2 then 0 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((541199538766136180500060791323 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (18 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then -7 else -1) else if j.val = 1 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 8) else if j.val = 2 then (if k.val = 0 then (16 : Int) else if k.val = 1 then -5 else if k.val = 2 then -6 else 2) else if j.val = 3 then (if k.val = 0 then (-44 : Int) else if k.val = 1 then 1 else if k.val = 2 then 7 else 8) else if j.val = 4 then (if k.val = 0 then (-31 : Int) else if k.val = 1 then -6 else if k.val = 2 then 4 else 7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808518911036262586789810398176 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (19 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 1) else if j.val = 1 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 2 then (if k.val = 0 then (4 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else 2) else if j.val = 3 then (if k.val = 0 then (5 : Int) else if k.val = 1 then -6 else if k.val = 2 then -2 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904175221132202471317967611203 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (20 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -7 else if k.val = 2 then -1 else -4) else if j.val = 2 then (if k.val = 0 then (15 : Int) else if k.val = 1 then 4 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811883867427553912989774248258 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (21 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -6) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (2 : Int) else if k.val = 1 then 1 else if k.val = 2 then 3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((814032403557763275163900023197 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (22 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 8) else if j.val = 1 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 2 then (if k.val = 0 then (24 : Int) else if k.val = 1 then -2 else if k.val = 2 then -7 else -2) else if j.val = 3 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 5 else if k.val = 2 then -2 else 8) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559944383554048000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (23 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((913522370876242217207826106794 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (24 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else if j.val = 1 then (if k.val = 0 then (18 : Int) else if k.val = 1 then -2 else if k.val = 2 then 3 else -8) else if j.val = 2 then (if k.val = 0 then (11 : Int) else if k.val = 1 then 3 else if k.val = 2 then -3 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945177489036000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (25 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559945289792332000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (26 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((695668838093712207982012101105 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (27 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else if j.val = 3 then (if k.val = 0 then (47 : Int) else if k.val = 1 then -4 else if k.val = 2 then -8 else -8) else if j.val = 4 then (if k.val = 0 then (8 : Int) else if k.val = 1 then 8 else if k.val = 2 then -3 else -6) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811591143840887347352170106515 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (28 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -4) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-9 : Int) else if k.val = 1 then 0 else if k.val = 2 then 6 else -4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911390606074637292430700376200 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (29 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else if j.val = 1 then (if k.val = 0 then (-13 : Int) else if k.val = 1 then -4 else if k.val = 2 then 2 else 5) else if j.val = 2 then (if k.val = 0 then (-27 : Int) else if k.val = 1 then 2 else if k.val = 2 then 8 else 1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180273322441013632000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (30 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((808205223588595511195970103295 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (31 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else -1) else if j.val = 1 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 2 then (if k.val = 0 then (7 : Int) else if k.val = 1 then -8 else if k.val = 2 then 2 else 0) else if j.val = 3 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then -6 else if k.val = 2 then 3 else -1) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((904534085314037229997629913908 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (32 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else 2) else if j.val = 1 then (if k.val = 0 then (29 : Int) else if k.val = 1 then -6 else if k.val = 2 then 1 else -8) else if j.val = 2 then (if k.val = 0 then (5 : Int) else if k.val = 1 then 2 else if k.val = 2 then -7 else 2) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559931868261136000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (33 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811315596387307490001439540566 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (34 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else -7) else if j.val = 1 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 2 then (if k.val = 0 then (17 : Int) else if k.val = 1 then -6 else if k.val = 2 then 6 else -8) else if j.val = 3 then (if k.val = 0 then (24 : Int) else if k.val = 1 then 5 else if k.val = 2 then -8 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((811854473535931708134213681349 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (35 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -7) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (3 : Int) else if k.val = 1 then 8 else if k.val = 2 then -1 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911579389640885564695560380105 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (36 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 5) else if j.val = 1 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 3 else if k.val = 2 then -2 else 4) else if j.val = 2 then (if k.val = 0 then (-32 : Int) else if k.val = 1 then 1 else if k.val = 2 then 6 else 5) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559944424711696000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (37 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((909032792488860497988015462724 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (38 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else if j.val = 1 then (if k.val = 0 then (-2 : Int) else if k.val = 1 then -3 else if k.val = 2 then -1 else 3) else if j.val = 2 then (if k.val = 0 then (-16 : Int) else if k.val = 1 then 8 else if k.val = 2 then 4 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559944790488832000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (39 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((693147180559943317223276000000 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (40 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else if j.val = 1 then (if k.val = 0 then (-1 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((705291444301061905613171790090 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (41 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 2 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else if j.val = 3 then (if k.val = 0 then (30 : Int) else if k.val = 1 then -5 else if k.val = 2 then 0 else -8) else if j.val = 4 then (if k.val = 0 then (-12 : Int) else if k.val = 1 then 8 else if k.val = 2 then 2 else -3) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((812102469345919673776447940217 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (42 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (23 : Int) else if k.val = 1 then -7 else if k.val = 2 then -3 else -4) else if j.val = 1 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 2 then (if k.val = 0 then (14 : Int) else if k.val = 1 then 7 else if k.val = 2 then -4 else -6) else if j.val = 3 then (if k.val = 0 then (-25 : Int) else if k.val = 1 then -7 else if k.val = 2 then 8 else 4) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) ∧
((911281219681316969557659200132 : ℚ)/10^30 ≤
      regFloorG (normQ (marginalCounts (m3 5) 0 (43 : Fin 88)))
        (fun (j : Fin 5) (k : Fin 4) => if j.val = 0 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else if j.val = 1 then (if k.val = 0 then (-17 : Int) else if k.val = 1 then 2 else if k.val = 2 then -4 else 8) else if j.val = 2 then (if k.val = 0 then (21 : Int) else if k.val = 1 then 2 else if k.val = 2 then -3 else -7) else (if k.val = 0 then (0 : Int) else if k.val = 1 then 0 else if k.val = 2 then 0 else 0))) := by sorry
