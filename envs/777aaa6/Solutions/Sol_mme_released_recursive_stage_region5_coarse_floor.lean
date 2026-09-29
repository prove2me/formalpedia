-- Prove2me | solution 1 for mme_released_recursive_stage_region5_coarse_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T05:18:20.974734+00:00
-- url     : https://prove2.me/submissions/7fbc335f-f4b5-487f-a4ff-95369f6d284e

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
import Theorems.Thm_mme_released_recursive_stage_region5_counts
import Theorems.Thm_mme_released_recursive_level3_coarse11
import Theorems.Thm_mme_released_recursive_level3_coarse12
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3Agg

/-- The certified floor numerator of each region, over the common denominator `10^30`. -/
def cfn (r : Fin 88) : ℕ := if r.val = 0 then 695666071826021116280564508112 else if r.val = 1 then 810515002463664360995393992159 else if r.val = 2 then 908502947935363354928522142625 else if r.val = 3 then 693147105845417780465023383110 else if r.val = 4 then 808121269446128009187287469177 else if r.val = 5 then 904325616033699840221917313855 else if r.val = 6 then 693147180559900619457232000000 else if r.val = 7 then 811387260541613574433574255248 else if r.val = 8 then 813667001534623803545524601408 else if r.val = 9 then 693147180559944823920076000000 else if r.val = 10 then 913641357128427516315373139679 else if r.val = 11 then 693147180559945280580332000000 else if r.val = 12 then 693147180559945290057232000000 else if r.val = 13 then 705297491018475363293517808845 else if r.val = 14 then 809570904621405270276514331153 else if r.val = 15 then 900203956605378915741441476193 else if r.val = 16 then 693146760684626987093523477428 else if r.val = 17 then 768086878270588868170666870668 else if r.val = 18 then 541199538766136180500060791323 else if r.val = 19 then 808518911036262586789810398176 else if r.val = 20 then 904175221132202471317967611203 else if r.val = 21 then 811883867427553912989774248258 else if r.val = 22 then 814032403557763275163900023197 else if r.val = 23 then 693147180559944383554048000000 else if r.val = 24 then 913522370876242217207826106794 else if r.val = 25 then 693147180559945177489036000000 else if r.val = 26 then 693147180559945289792332000000 else if r.val = 27 then 695668838093712207982012101105 else if r.val = 28 then 811591143840887347352170106515 else if r.val = 29 then 911390606074637292430700376200 else if r.val = 30 then 693147180273322441013632000000 else if r.val = 31 then 808205223588595511195970103295 else if r.val = 32 then 904534085314037229997629913908 else if r.val = 33 then 693147180559931868261136000000 else if r.val = 34 then 811315596387307490001439540566 else if r.val = 35 then 811854473535931708134213681349 else if r.val = 36 then 911579389640885564695560380105 else if r.val = 37 then 693147180559944424711696000000 else if r.val = 38 then 909032792488860497988015462724 else if r.val = 39 then 693147180559944790488832000000 else if r.val = 40 then 693147180559943317223276000000 else if r.val = 41 then 705291444301061905613171790090 else if r.val = 42 then 812102469345919673776447940217 else if r.val = 43 then 911281219681316969557659200132 else if r.val = 44 then 693147180266420149021456000000 else if r.val = 45 then 768102556877844962917901709025 else if r.val = 46 then 541198116343397117553207884524 else if r.val = 47 then 808683667607366472667482532317 else if r.val = 48 then 904413262095063070005879942846 else if r.val = 49 then 693147180559929518478988000000 else if r.val = 50 then 811798208270044986931885710714 else if r.val = 51 then 809089132515943113551386430545 else if r.val = 52 then 911347646085047168314122014589 else if r.val = 53 then 693147180559944173592428000000 else if r.val = 54 then 900617757476034444852246704497 else if r.val = 55 then 693147180559943449910348000000 else if r.val = 56 then 693147180542088836538368000000 else if r.val = 57 then 711921456007666069149017737618 else if r.val = 58 then 810280142875855469619486393837 else if r.val = 59 then 900154992375473884443010729163 else if r.val = 60 then 693146761385172073979894325154 else if r.val = 61 then 769438887704919833996436612058 else if r.val = 62 then 555873005991276118248273494768 else if r.val = 63 then 809276489908632946218859847096 else if r.val = 64 then 904045326127264417377368830673 else if r.val = 65 then 812624437913871542028681427300 else if r.val = 66 then 812705306402576688855828896235 else if r.val = 67 then 911405261478654970513834985006 else if r.val = 68 then 693147180559945293063296000000 else if r.val = 69 then 908840170119423660381882770641 else if r.val = 70 then 693147180559945174625132000000 else if r.val = 71 then 693147180559945243352848000000 else if r.val = 72 then 712048499720068437650045688140 else if r.val = 73 then 811733738370894701068722619082 else if r.val = 74 then 908313610686761209962150485393 else if r.val = 75 then 693147113445299261519333289629 else if r.val = 76 then 769450689114141276112009414139 else if r.val = 77 then 555872924182558188973808265606 else if r.val = 78 then 809348295410438111267194843583 else if r.val = 79 then 904235199227354041745131282040 else if r.val = 80 then 693147180559795534225168000000 else if r.val = 81 then 812602099580710984207856319195 else if r.val = 82 then 809595600031994803718498212339 else if r.val = 83 then 911286639355110921740949111706 else if r.val = 84 then 693147180559942237375756000000 else if r.val = 85 then 900562880996485096144985407787 else if r.val = 86 then 693147180558117897512108000000 else if r.val = 87 then 693147180529161521174636000000 else 0

/-- A single region's certificate, turned into a bound on its entropy. -/
theorem cstep {r : Fin 88} {e : Fin 5 → Fin 4 → ℤ} {q : ℚ}
    (h : q ≤ regFloorG (normQ (marginalCounts (m3 5) 0 r)) e) :
    ((q : ℚ) : ℝ) ≤
      entropy (fun j ↦ ((normQ (marginalCounts (m3 5) 0 r) j : ℚ) : ℝ)) :=
  le_trans (by exact_mod_cast h)
    (mme_certified_entropy_rational_floor.1 (normQ (marginalCounts (m3 5) 0 r))
      (fun j ↦ mme_certified_entropy_bridge.{0, 0}.2.2.2.2.1 (marginalCounts (m3 5) 0 r) j)
      e _ _ rfl (fun _ ↦ rfl))

theorem hent : ∀ r : Fin 88,
    ((cfn r : ℕ) : ℝ)/10^30 ≤
      entropy (fun j ↦ ((normQ (marginalCounts (m3 5) 0 r) j : ℚ) : ℝ)) := by
  intro r
  match r with
  | ⟨0, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.1
  | ⟨1, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.1
  | ⟨2, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.1
  | ⟨3, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.1
  | ⟨4, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.1
  | ⟨5, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.1
  | ⟨6, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.1
  | ⟨7, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.1
  | ⟨8, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.1
  | ⟨9, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.1
  | ⟨10, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.1
  | ⟨11, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨12, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨13, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨14, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨15, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨16, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨17, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨18, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨19, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨20, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨21, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨22, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨23, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨24, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨25, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨26, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨27, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨28, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨29, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨30, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨31, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨32, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨33, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨34, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨35, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨36, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨37, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨38, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨39, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨40, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨41, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨42, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨43, _⟩ => simpa using cstep mme_released_recursive_level3_coarse11.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | ⟨44, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.1
  | ⟨45, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.1
  | ⟨46, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.1
  | ⟨47, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.1
  | ⟨48, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.1
  | ⟨49, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.1
  | ⟨50, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.1
  | ⟨51, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.1
  | ⟨52, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.1
  | ⟨53, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.1
  | ⟨54, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.1
  | ⟨55, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨56, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨57, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨58, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨59, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨60, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨61, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨62, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨63, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨64, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨65, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨66, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨67, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨68, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨69, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨70, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨71, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨72, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨73, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨74, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨75, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨76, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨77, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨78, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨79, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨80, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨81, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨82, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨83, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨84, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨85, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨86, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨87, _⟩ => simpa using cstep mme_released_recursive_level3_coarse12.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | ⟨n + 88, h⟩ => exact absurd h (by omega)

/-- The weighted total, as one natural number. -/
theorem hsum : ∑ r : Fin 88, n3 5 r * cfn r = 737581360296765050632407220698715100754686381400609577000000000000000000000000000000000000 := by decide +kernel

end L3Agg

theorem solution :
    ((737581360296765050632407220698715100754686381400609577000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 ≤ coarsePotential (m3 5) 0 := by
  have hc := mme_released_recursive_stage_region5_counts
  have hpos : ∀ r, 0 < ∑ j, marginalCounts (m3 5) 0 r j := by
    intro r
    rw [mme_certified_rate_entry.{0}.1 (m3 5) 0 r, hc.2 r]
    exact hc.1 r
  have hw : ∀ r, (∑ j, marginalCounts (m3 5) 0 r j) = n3 5 r := by
    intro r
    rw [mme_certified_rate_entry.{0}.1 (m3 5) 0 r, hc.2 r]
  rw [mme_certified_entropy_bridge.{0, 0}.2.2.2.2.2 (m3 5) 0 hpos]
  have hterm : ∀ r : Fin 88,
      ((n3 5 r * L3Agg.cfn r : ℕ) : ℝ)/10^30 ≤
        ((∑ j, marginalCounts (m3 5) 0 r j : ℕ) : ℝ) *
          entropy (fun j ↦ ((normQ (marginalCounts (m3 5) 0 r) j : ℚ) : ℝ)) := by
    intro r
    rw [hw r]
    have h1 := L3Agg.hent r
    have h2 : (0 : ℝ) ≤ ((n3 5 r : ℕ) : ℝ) := by positivity
    calc ((n3 5 r * L3Agg.cfn r : ℕ) : ℝ)/10^30
        = ((n3 5 r : ℕ) : ℝ) * (((L3Agg.cfn r : ℕ) : ℝ)/10^30) := by push_cast; ring
      _ ≤ ((n3 5 r : ℕ) : ℝ) * entropy _ := mul_le_mul_of_nonneg_left h1 h2
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun r _ ↦ hterm r))
  rw [← Finset.sum_div, ← Nat.cast_sum, L3Agg.hsum]
