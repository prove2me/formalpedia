-- Prove2me | solution 1 for mme_released_recursive_stage_region4_coarse_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T05:14:51.318988+00:00
-- url     : https://prove2.me/submissions/7158acfc-fbdd-4e35-9346-8d618c051aee

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_certified_generic_floor_data
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_entropy_rational_floor
import Theorems.Thm_mme_certified_rate_entry
import Theorems.Thm_mme_released_recursive_stage_region4_counts
import Theorems.Thm_mme_released_recursive_level3_coarse9
import Theorems.Thm_mme_released_recursive_level3_coarse10
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3Agg

/-- The certified floor numerator of each region, over the common denominator `10^30`. -/
def cfn (r : Fin 88) : ℕ := if r.val = 0 then 695669369271058284567787966781 else if r.val = 1 then 811853802924915988459743364486 else if r.val = 2 then 909028802561712503675482039394 else if r.val = 3 then 693147125745428790457875602407 else if r.val = 4 then 811315135345153628435154288720 else if r.val = 5 then 911570245883450418890941477203 else if r.val = 6 then 693147180559945034852332000000 else if r.val = 7 then 808245403451173076401937082854 else if r.val = 8 then 693147180559945291133056000000 else if r.val = 9 then 811596422819819972301783649462 else if r.val = 10 then 904526051801826186618685990665 else if r.val = 11 then 911391733358412288973669122010 else if r.val = 12 then 693147180559943248075628000000 else if r.val = 13 then 693147180559945297569868000000 else if r.val = 14 then 705302718657212482970351087589 else if r.val = 15 then 768122001448974932684734835875 else if r.val = 16 then 809134773132695634560864335090 else if r.val = 17 then 900610304103560969829806931246 else if r.val = 18 then 693146831513764335565064694636 else if r.val = 19 then 541185030310113003149889450570 else if r.val = 20 then 811799288703544469931333685812 else if r.val = 21 then 911343963373787536139146831205 else if r.val = 22 then 693147180559945059081548000000 else if r.val = 23 then 808689015859258705557281359923 else if r.val = 24 then 693147180559944889822976000000 else if r.val = 25 then 812097632779688235913446814819 else if r.val = 26 then 904408159415713284658404201478 else if r.val = 27 then 911281309933911292955216068470 else if r.val = 28 then 693147180559943233885868000000 else if r.val = 29 then 693147180559945297666048000000 else if r.val = 30 then 695670881237055574086707642991 else if r.val = 31 then 813661635104783897440245740584 else if r.val = 32 then 913639102893697258136557809038 else if r.val = 33 then 693147175096488814038028000000 else if r.val = 34 then 811377522406426906244615507773 else if r.val = 35 then 693147180559945298880716000000 else if r.val = 36 then 808083922188805489925780196523 else if r.val = 37 then 693147180559945170271616000000 else if r.val = 38 then 810510024149896048286767809858 else if r.val = 39 then 904413986296019121309740468186 else if r.val = 40 then 908495916247890182422996443557 else if r.val = 41 then 693147180559943131888336000000 else if r.val = 42 then 693147180559943259682156000000 else if r.val = 43 then 705299089213330417227946216475 else if r.val = 44 then 768127764301229741304997858058 else if r.val = 45 then 814051919860347967453034530207 else if r.val = 46 then 913523074985922241635849950810 else if r.val = 47 then 693147176320240717253036000000 else if r.val = 48 then 541180737380624197153392581904 else if r.val = 49 then 811877301077083471639443609560 else if r.val = 50 then 693147180557850018427088000000 else if r.val = 51 then 808497084789076486700589988053 else if r.val = 52 then 693147180559945169515648000000 else if r.val = 53 then 809606773586689517385998719850 else if r.val = 54 then 904101392715791484866693310392 else if r.val = 55 then 900199270264291755529499818451 else if r.val = 56 then 693147035098486360120508801025 else if r.val = 57 then 711920765226528674414692795685 else if r.val = 58 then 769499588009452763230169921478 else if r.val = 59 then 809613051837585436886761574279 else if r.val = 60 then 900553977589347009069508420834 else if r.val = 61 then 693146832004325337769191326700 else if r.val = 62 then 555861117124767761723585701433 else if r.val = 63 then 812598407739909718941214269880 else if r.val = 64 then 911273294943225870210586493818 else if r.val = 65 then 693147180559934353608332000000 else if r.val = 66 then 809334046260627355902765110426 else if r.val = 67 then 693147180559943320614016000000 else if r.val = 68 then 811730108517287143723935714060 else if r.val = 69 then 904173537277117988515101760103 else if r.val = 70 then 908308807483168200389391263148 else if r.val = 71 then 693147180559945176706832000000 else if r.val = 72 then 693147180559945229850832000000 else if r.val = 73 then 712047937852289715885666312985 else if r.val = 74 then 769485884848233496374812645712 else if r.val = 75 then 812699318882261418586821284031 else if r.val = 76 then 908834842071177326249467244559 else if r.val = 77 then 693147126156656193543936308395 else if r.val = 78 then 555860243632069264890026838967 else if r.val = 79 then 812616744654764801123986716370 else if r.val = 80 then 911391161240935185140221050852 else if r.val = 81 then 693147180559945024280236000000 else if r.val = 82 then 809263012016830707453111634956 else if r.val = 83 then 693147180559945273176832000000 else if r.val = 84 then 810301755187771029935204828691 else if r.val = 85 then 904069347799499958805262237154 else if r.val = 86 then 900150591845555583510334824602 else if r.val = 87 then 693147033294038099932950429760 else 0

/-- A single region's certificate, turned into a bound on its entropy. -/
theorem cstep {r : Fin 88} {e : Fin 5 → Fin 4 → ℤ} {q : ℚ}
    (h : q ≤ regFloorG (normQ (marginalCounts (m3 4) 0 r)) e) :
    ((q : ℚ) : ℝ) ≤
      entropy (fun j ↦ ((normQ (marginalCounts (m3 4) 0 r) j : ℚ) : ℝ)) :=
  le_trans (by exact_mod_cast h)
    (mme_certified_entropy_rational_floor.1 (normQ (marginalCounts (m3 4) 0 r))
      (fun j ↦ mme_certified_entropy_bridge.{0, 0}.2.2.2.2.1 (marginalCounts (m3 4) 0 r) j)
      e _ _ rfl (fun _ ↦ rfl))

theorem hent : ∀ r : Fin 88,
    ((cfn r : ℕ) : ℝ)/10^30 ≤
      entropy (fun j ↦ ((normQ (marginalCounts (m3 4) 0 r) j : ℚ) : ℝ)) := by
  intro r
  match r with
  | ⟨0, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.1
  | ⟨1, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.1
  | ⟨2, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.1
  | ⟨3, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.1
  | ⟨4, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.1
  | ⟨5, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.1
  | ⟨6, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.1
  | ⟨7, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.1
  | ⟨8, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.1
  | ⟨9, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.1
  | ⟨10, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.1
  | ⟨11, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨12, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨13, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨14, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨15, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨16, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨17, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨18, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨19, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨20, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨21, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨22, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨23, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨24, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨25, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨26, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨27, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨28, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨29, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨30, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨31, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨32, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨33, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨34, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨35, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨36, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨37, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨38, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨39, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨40, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨41, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨42, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨43, _⟩ => simpa using cstep mme_released_recursive_level3_coarse9.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | ⟨44, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.1
  | ⟨45, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.1
  | ⟨46, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.1
  | ⟨47, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.1
  | ⟨48, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.1
  | ⟨49, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.1
  | ⟨50, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.1
  | ⟨51, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.1
  | ⟨52, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.1
  | ⟨53, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.1
  | ⟨54, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.1
  | ⟨55, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨56, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨57, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨58, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨59, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨60, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨61, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨62, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨63, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨64, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨65, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨66, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨67, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨68, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨69, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨70, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨71, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨72, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨73, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨74, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨75, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨76, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨77, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨78, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨79, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨80, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨81, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨82, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨83, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨84, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨85, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨86, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨87, _⟩ => simpa using cstep mme_released_recursive_level3_coarse10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | ⟨n + 88, h⟩ => exact absurd h (by omega)

/-- The weighted total, as one natural number. -/
theorem hsum : ∑ r : Fin 88, n3 4 r * cfn r = 739517600610609651326593771391531763774544795901863690000000000000000000000000000000000000 := by decide +kernel

end L3Agg

theorem solution :
    ((739517600610609651326593771391531763774544795901863690000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 ≤ coarsePotential (m3 4) 0 := by
  have hc := mme_released_recursive_stage_region4_counts
  have hpos : ∀ r, 0 < ∑ j, marginalCounts (m3 4) 0 r j := by
    intro r
    rw [mme_certified_rate_entry.{0}.1 (m3 4) 0 r, hc.2 r]
    exact hc.1 r
  have hw : ∀ r, (∑ j, marginalCounts (m3 4) 0 r j) = n3 4 r := by
    intro r
    rw [mme_certified_rate_entry.{0}.1 (m3 4) 0 r, hc.2 r]
  rw [mme_certified_entropy_bridge.{0, 0}.2.2.2.2.2 (m3 4) 0 hpos]
  have hterm : ∀ r : Fin 88,
      ((n3 4 r * L3Agg.cfn r : ℕ) : ℝ)/10^30 ≤
        ((∑ j, marginalCounts (m3 4) 0 r j : ℕ) : ℝ) *
          entropy (fun j ↦ ((normQ (marginalCounts (m3 4) 0 r) j : ℚ) : ℝ)) := by
    intro r
    rw [hw r]
    have h1 := L3Agg.hent r
    have h2 : (0 : ℝ) ≤ ((n3 4 r : ℕ) : ℝ) := by positivity
    calc ((n3 4 r * L3Agg.cfn r : ℕ) : ℝ)/10^30
        = ((n3 4 r : ℕ) : ℝ) * (((L3Agg.cfn r : ℕ) : ℝ)/10^30) := by push_cast; ring
      _ ≤ ((n3 4 r : ℕ) : ℝ) * entropy _ := mul_le_mul_of_nonneg_left h1 h2
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun r _ ↦ hterm r))
  rw [← Finset.sum_div, ← Nat.cast_sum, L3Agg.hsum]
