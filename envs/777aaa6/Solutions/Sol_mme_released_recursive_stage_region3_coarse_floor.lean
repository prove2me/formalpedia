-- Prove2me | solution 1 for mme_released_recursive_stage_region3_coarse_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T05:11:09.628268+00:00
-- url     : https://prove2.me/submissions/89055593-6805-49a6-a554-6be225a72366

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
import Theorems.Thm_mme_released_recursive_stage_region3_counts
import Theorems.Thm_mme_released_recursive_level3_coarse7
import Theorems.Thm_mme_released_recursive_level3_coarse8
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3Agg

/-- The certified floor numerator of each region, over the common denominator `10^30`. -/
def cfn (r : Fin 88) : ℕ := if r.val = 0 then 693147180559803918376832000000 else if r.val = 1 then 900198772144446986280378918452 else if r.val = 2 then 809572757342241000326540784847 else if r.val = 3 then 706244616860428601677584163001 else if r.val = 4 then 904095863401913899910704952015 else if r.val = 5 then 808520137104824785748818701813 else if r.val = 6 then 541187341076757881927365920493 else if r.val = 7 then 768097625658495294393189895072 else if r.val = 8 then 811882622469538794631750290814 else if r.val = 9 then 693147180559944370117328000000 else if r.val = 10 then 814030551326096819110610031306 else if r.val = 11 then 693147180559935313016908000000 else if r.val = 12 then 913526140279325342642222454692 else if r.val = 13 then 693147180559945309400848000000 else if r.val = 14 then 693147168914143280604127111187 else if r.val = 15 then 908484475270165228621648414939 else if r.val = 16 then 810514281374404679741913313743 else if r.val = 17 then 697127468386573497166906137825 else if r.val = 18 then 693147180559933446722176000000 else if r.val = 19 then 904429780739577679940109033101 else if r.val = 20 then 808083972356323530416707250216 else if r.val = 21 then 811371749203331382662822200825 else if r.val = 22 then 693147180559944874361068000000 else if r.val = 23 then 813673075467826651641723969899 else if r.val = 24 then 693147180559945309227136000000 else if r.val = 25 then 913642270904277565405343132922 else if r.val = 26 then 693147180559945309390336000000 else if r.val = 27 then 693147180559791314391148000000 else if r.val = 28 then 900152877269033763091569668172 else if r.val = 29 then 810306504006677292317071196718 else if r.val = 30 then 712146575508345991781549688711 else if r.val = 31 then 904177225202485509527202691263 else if r.val = 32 then 809257370939581445485329731107 else if r.val = 33 then 555843590143552827749298012976 else if r.val = 34 then 769476886099228430436853893788 else if r.val = 35 then 812621575366290606299751892203 else if r.val = 36 then 693147180559942392985216000000 else if r.val = 37 then 911395365800123150981057887990 else if r.val = 38 then 812699634577876763815341478254 else if r.val = 39 then 693147180559945307540332000000 else if r.val = 40 then 908850301444032893060745765169 else if r.val = 41 then 693147180559943341962496000000 else if r.val = 42 then 693147169135663465199799345430 else if r.val = 43 then 908309660957592116655410292229 else if r.val = 44 then 811738826423617516601147463446 else if r.val = 45 then 712146542342568988596734160723 else if r.val = 46 then 693147180559945255512268000000 else if r.val = 47 then 904254720801754692197714324568 else if r.val = 48 then 809315840138592354642185041458 else if r.val = 49 then 555844521317842289261618599517 else if r.val = 50 then 769489356564780416006761472109 else if r.val = 51 then 812598642439757556960352944846 else if r.val = 52 then 693147180559945289916176000000 else if r.val = 53 then 911278722580535173185648643961 else if r.val = 54 then 809595159104823034755290855932 else if r.val = 55 then 693147180559943504017132000000 else if r.val = 56 then 900550196731689284945575211850 else if r.val = 57 then 693147180541225357274896000000 else if r.val = 58 then 693147180390761543488876000000 else if r.val = 59 then 911388518708382106244654971108 else if r.val = 60 then 811598413097260483392200981697 else if r.val = 61 then 697126321703030219482663298366 else if r.val = 62 then 693147180559939060830928000000 else if r.val = 63 then 904597937252373092971840113474 else if r.val = 64 then 808186764394569676979847257225 else if r.val = 65 then 811300502732963624416274518245 else if r.val = 66 then 693147180559944189845632000000 else if r.val = 67 then 911569915924347837091083072839 else if r.val = 68 then 811850267868077535990056290899 else if r.val = 69 then 693147180559945286854732000000 else if r.val = 70 then 909012658556372344211020000581 else if r.val = 71 then 693147180559945243742416000000 else if r.val = 72 then 693147180390792394842832000000 else if r.val = 73 then 911279093029285491113712937749 else if r.val = 74 then 812100135146387107807755506507 else if r.val = 75 then 706033608710057132343222737078 else if r.val = 76 then 693147180559911033338188000000 else if r.val = 77 then 904472607784077603947225350499 else if r.val = 78 then 808679185980878984352410362354 else if r.val = 79 then 541183177621849251629516045980 else if r.val = 80 then 768144305827121405544249696658 else if r.val = 81 then 811791171740572351750044580664 else if r.val = 82 then 693147180559943067394732000000 else if r.val = 83 then 911349439256430833369959519312 else if r.val = 84 then 809096359233803228298592370905 else if r.val = 85 then 693147180559921835500288000000 else if r.val = 86 then 900621904023980412778549552562 else if r.val = 87 then 693147180530278746740428000000 else 0

/-- A single region's certificate, turned into a bound on its entropy. -/
theorem cstep {r : Fin 88} {e : Fin 5 → Fin 4 → ℤ} {q : ℚ}
    (h : q ≤ regFloorG (normQ (marginalCounts (m3 3) 0 r)) e) :
    ((q : ℚ) : ℝ) ≤
      entropy (fun j ↦ ((normQ (marginalCounts (m3 3) 0 r) j : ℚ) : ℝ)) :=
  le_trans (by exact_mod_cast h)
    (mme_certified_entropy_rational_floor.1 (normQ (marginalCounts (m3 3) 0 r))
      (fun j ↦ mme_certified_entropy_bridge.{0, 0}.2.2.2.2.1 (marginalCounts (m3 3) 0 r) j)
      e _ _ rfl (fun _ ↦ rfl))

theorem hent : ∀ r : Fin 88,
    ((cfn r : ℕ) : ℝ)/10^30 ≤
      entropy (fun j ↦ ((normQ (marginalCounts (m3 3) 0 r) j : ℚ) : ℝ)) := by
  intro r
  match r with
  | ⟨0, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.1
  | ⟨1, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.1
  | ⟨2, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.1
  | ⟨3, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.1
  | ⟨4, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.1
  | ⟨5, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.1
  | ⟨6, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.1
  | ⟨7, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.1
  | ⟨8, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.1
  | ⟨9, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.1
  | ⟨10, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.1
  | ⟨11, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨12, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨13, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨14, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨15, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨16, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨17, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨18, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨19, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨20, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨21, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨22, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨23, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨24, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨25, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨26, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨27, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨28, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨29, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨30, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨31, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨32, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨33, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨34, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨35, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨36, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨37, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨38, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨39, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨40, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨41, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨42, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨43, _⟩ => simpa using cstep mme_released_recursive_level3_coarse7.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | ⟨44, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.1
  | ⟨45, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.1
  | ⟨46, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.1
  | ⟨47, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.1
  | ⟨48, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.1
  | ⟨49, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.1
  | ⟨50, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.1
  | ⟨51, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.1
  | ⟨52, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.1
  | ⟨53, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.1
  | ⟨54, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.1
  | ⟨55, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨56, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨57, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨58, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨59, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨60, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨61, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨62, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨63, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨64, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨65, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨66, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨67, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨68, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨69, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨70, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨71, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨72, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨73, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨74, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨75, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨76, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨77, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨78, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨79, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨80, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨81, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨82, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨83, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨84, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨85, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨86, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨87, _⟩ => simpa using cstep mme_released_recursive_level3_coarse8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | ⟨n + 88, h⟩ => exact absurd h (by omega)

/-- The weighted total, as one natural number. -/
theorem hsum : ∑ r : Fin 88, n3 3 r * cfn r = 734168275669611927498658348229920902206900750308205885000000000000000000000000000000000000 := by decide +kernel

end L3Agg

theorem solution :
    ((734168275669611927498658348229920902206900750308205885000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 ≤ coarsePotential (m3 3) 0 := by
  have hc := mme_released_recursive_stage_region3_counts
  have hpos : ∀ r, 0 < ∑ j, marginalCounts (m3 3) 0 r j := by
    intro r
    rw [mme_certified_rate_entry.{0}.1 (m3 3) 0 r, hc.2 r]
    exact hc.1 r
  have hw : ∀ r, (∑ j, marginalCounts (m3 3) 0 r j) = n3 3 r := by
    intro r
    rw [mme_certified_rate_entry.{0}.1 (m3 3) 0 r, hc.2 r]
  rw [mme_certified_entropy_bridge.{0, 0}.2.2.2.2.2 (m3 3) 0 hpos]
  have hterm : ∀ r : Fin 88,
      ((n3 3 r * L3Agg.cfn r : ℕ) : ℝ)/10^30 ≤
        ((∑ j, marginalCounts (m3 3) 0 r j : ℕ) : ℝ) *
          entropy (fun j ↦ ((normQ (marginalCounts (m3 3) 0 r) j : ℚ) : ℝ)) := by
    intro r
    rw [hw r]
    have h1 := L3Agg.hent r
    have h2 : (0 : ℝ) ≤ ((n3 3 r : ℕ) : ℝ) := by positivity
    calc ((n3 3 r * L3Agg.cfn r : ℕ) : ℝ)/10^30
        = ((n3 3 r : ℕ) : ℝ) * (((L3Agg.cfn r : ℕ) : ℝ)/10^30) := by push_cast; ring
      _ ≤ ((n3 3 r : ℕ) : ℝ) * entropy _ := mul_le_mul_of_nonneg_left h1 h2
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun r _ ↦ hterm r))
  rw [← Finset.sum_div, ← Nat.cast_sum, L3Agg.hsum]
