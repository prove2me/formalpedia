-- Prove2me | solution 1 for mme_released_recursive_stage_region2_coarse_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T05:06:38.243409+00:00
-- url     : https://prove2.me/submissions/a467a3b7-b807-4672-89b7-429da0fd8999

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
import Theorems.Thm_mme_released_recursive_stage_region2_counts
import Theorems.Thm_mme_released_recursive_level3_coarse5
import Theorems.Thm_mme_released_recursive_level3_coarse6
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3Agg

/-- The certified floor numerator of each region, over the common denominator `10^30`. -/
def cfn (r : Fin 88) : ℕ := if r.val = 0 then 693147180558762148513408000000 else if r.val = 1 then 900606953945300249007160017299 else if r.val = 2 then 809119023502253687948346943358 else if r.val = 3 then 768116008138505063704479108481 else if r.val = 4 then 706219557913212491135269294454 else if r.val = 5 then 693147180559943258233132000000 else if r.val = 6 then 911339480323526764138936731773 else if r.val = 7 then 811798508532713228129782555253 else if r.val = 8 then 541178450878247079133359493163 else if r.val = 9 then 693147180559942689205888000000 else if r.val = 10 then 808704584262096538860998395196 else if r.val = 11 then 904424797981791683049772775879 else if r.val = 12 then 812097993263937924166775814155 else if r.val = 13 then 693147180559941429871436000000 else if r.val = 14 then 911275171576298103454178452596 else if r.val = 15 then 693147180559945302138028000000 else if r.val = 16 then 693147180559326566710828000000 else if r.val = 17 then 909012132731725726201716712622 else if r.val = 18 then 811856599308900756608059088533 else if r.val = 19 then 697126399606435983233741102401 else if r.val = 20 then 693147180559940564962832000000 else if r.val = 21 then 911562184308361680285160353913 else if r.val = 22 then 811299770747290279368580825761 else if r.val = 23 then 693147180559945308764368000000 else if r.val = 24 then 808180930404550404533313013645 else if r.val = 25 then 904522238274069697882955230274 else if r.val = 26 then 811591678074178562878123673624 else if r.val = 27 then 693147180559943302198028000000 else if r.val = 28 then 911384503655058441783277643238 else if r.val = 29 then 693147180559945296312832000000 else if r.val = 30 then 693147180558940764264332000000 else if r.val = 31 then 900552667508118664644817163406 else if r.val = 32 then 809577215803503972341562651208 else if r.val = 33 then 769512253510153480225725085640 else if r.val = 34 then 712145727192566555421992007777 else if r.val = 35 then 693147180559945164696332000000 else if r.val = 36 then 911281151713468212154711718910 else if r.val = 37 then 812592966432752933334503107921 else if r.val = 38 then 555841011321014167864728120306 else if r.val = 39 then 693147180559945054695632000000 else if r.val = 40 then 809333291365254448967396313124 else if r.val = 41 then 904267399913155323761571295837 else if r.val = 42 then 811736569838565319927843453778 else if r.val = 43 then 693147180559935903520976000000 else if r.val = 44 then 908325359119530596334407931475 else if r.val = 45 then 693147180559943273061356000000 else if r.val = 46 then 693147155156113274603046306473 else if r.val = 47 then 908832442499560987486825367967 else if r.val = 48 then 812705119321585476734271786928 else if r.val = 49 then 769499735418699768720615863817 else if r.val = 50 then 712145688982461635277570329004 else if r.val = 51 then 693147180559945056797996000000 else if r.val = 52 then 911389002611906535961335434213 else if r.val = 53 then 812610097014610981038876394507 else if r.val = 54 then 555839262800797352193228774017 else if r.val = 55 then 693147180559945225548268000000 else if r.val = 56 then 809254626938009287581158899794 else if r.val = 57 then 904174067446698632161002067269 else if r.val = 58 then 810262922464722712891004123417 else if r.val = 59 then 900135090685415182621685350433 else if r.val = 60 then 693147032565648941175148952256 else if r.val = 61 then 693147177777170961385168000000 else if r.val = 62 then 913635271692005838891910421335 else if r.val = 63 then 813666032907065811261810639461 else if r.val = 64 then 697107702383598967852042279033 else if r.val = 65 then 693147180559940541238528000000 else if r.val = 66 then 811363495015077106383636213823 else if r.val = 67 then 693147180559945295667968000000 else if r.val = 68 then 808063973333190131823627888319 else if r.val = 69 then 904442706875552098961590574012 else if r.val = 70 then 810505974110958074747758371608 else if r.val = 71 then 693147180559933105796332000000 else if r.val = 72 then 908478667143893967840054705234 else if r.val = 73 then 693147180559945298354956000000 else if r.val = 74 then 693147177778038558778576000000 else if r.val = 75 then 913523360619795756146835727666 else if r.val = 76 then 814027245896503449218869586820 else if r.val = 77 then 768128973218896905742050088500 else if r.val = 78 then 706244786852125191721474325205 else if r.val = 79 then 693147180559917386338828000000 else if r.val = 80 then 811866072115054199250437015241 else if r.val = 81 then 541172579877544830047349695708 else if r.val = 82 then 693147180559943876340496000000 else if r.val = 83 then 808497660291525475555814380364 else if r.val = 84 then 904271063551114303975859915889 else if r.val = 85 then 809596572386078316263144968264 else if r.val = 86 then 900203948629792680361522546310 else if r.val = 87 then 693147031671891987757848793744 else 0

/-- A single region's certificate, turned into a bound on its entropy. -/
theorem cstep {r : Fin 88} {e : Fin 5 → Fin 4 → ℤ} {q : ℚ}
    (h : q ≤ regFloorG (normQ (marginalCounts (m3 2) 0 r)) e) :
    ((q : ℚ) : ℝ) ≤
      entropy (fun j ↦ ((normQ (marginalCounts (m3 2) 0 r) j : ℚ) : ℝ)) :=
  le_trans (by exact_mod_cast h)
    (mme_certified_entropy_rational_floor.1 (normQ (marginalCounts (m3 2) 0 r))
      (fun j ↦ mme_certified_entropy_bridge.{0, 0}.2.2.2.2.1 (marginalCounts (m3 2) 0 r) j)
      e _ _ rfl (fun _ ↦ rfl))

theorem hent : ∀ r : Fin 88,
    ((cfn r : ℕ) : ℝ)/10^30 ≤
      entropy (fun j ↦ ((normQ (marginalCounts (m3 2) 0 r) j : ℚ) : ℝ)) := by
  intro r
  match r with
  | ⟨0, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.1
  | ⟨1, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.1
  | ⟨2, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.1
  | ⟨3, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.1
  | ⟨4, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.1
  | ⟨5, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.1
  | ⟨6, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.1
  | ⟨7, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.1
  | ⟨8, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.1
  | ⟨9, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.1
  | ⟨10, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.1
  | ⟨11, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨12, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨13, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨14, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨15, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨16, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨17, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨18, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨19, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨20, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨21, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨22, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨23, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨24, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨25, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨26, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨27, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨28, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨29, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨30, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨31, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨32, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨33, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨34, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨35, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨36, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨37, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨38, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨39, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨40, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨41, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨42, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨43, _⟩ => simpa using cstep mme_released_recursive_level3_coarse5.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | ⟨44, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.1
  | ⟨45, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.1
  | ⟨46, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.1
  | ⟨47, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.1
  | ⟨48, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.1
  | ⟨49, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.1
  | ⟨50, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.1
  | ⟨51, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.1
  | ⟨52, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.1
  | ⟨53, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.1
  | ⟨54, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.1
  | ⟨55, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨56, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨57, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨58, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨59, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨60, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨61, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨62, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨63, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨64, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨65, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨66, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨67, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨68, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨69, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨70, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨71, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨72, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨73, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨74, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨75, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨76, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨77, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨78, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨79, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨80, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨81, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨82, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨83, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨84, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨85, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨86, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨87, _⟩ => simpa using cstep mme_released_recursive_level3_coarse6.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | ⟨n + 88, h⟩ => exact absurd h (by omega)

/-- The weighted total, as one natural number. -/
theorem hsum : ∑ r : Fin 88, n3 2 r * cfn r = 735444397684308737129328950271921984408657265610625066000000000000000000000000000000000000 := by decide +kernel

end L3Agg

theorem solution :
    ((735444397684308737129328950271921984408657265610625066000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 ≤ coarsePotential (m3 2) 0 := by
  have hc := mme_released_recursive_stage_region2_counts
  have hpos : ∀ r, 0 < ∑ j, marginalCounts (m3 2) 0 r j := by
    intro r
    rw [mme_certified_rate_entry.{0}.1 (m3 2) 0 r, hc.2 r]
    exact hc.1 r
  have hw : ∀ r, (∑ j, marginalCounts (m3 2) 0 r j) = n3 2 r := by
    intro r
    rw [mme_certified_rate_entry.{0}.1 (m3 2) 0 r, hc.2 r]
  rw [mme_certified_entropy_bridge.{0, 0}.2.2.2.2.2 (m3 2) 0 hpos]
  have hterm : ∀ r : Fin 88,
      ((n3 2 r * L3Agg.cfn r : ℕ) : ℝ)/10^30 ≤
        ((∑ j, marginalCounts (m3 2) 0 r j : ℕ) : ℝ) *
          entropy (fun j ↦ ((normQ (marginalCounts (m3 2) 0 r) j : ℚ) : ℝ)) := by
    intro r
    rw [hw r]
    have h1 := L3Agg.hent r
    have h2 : (0 : ℝ) ≤ ((n3 2 r : ℕ) : ℝ) := by positivity
    calc ((n3 2 r * L3Agg.cfn r : ℕ) : ℝ)/10^30
        = ((n3 2 r : ℕ) : ℝ) * (((L3Agg.cfn r : ℕ) : ℝ)/10^30) := by push_cast; ring
      _ ≤ ((n3 2 r : ℕ) : ℝ) * entropy _ := mul_le_mul_of_nonneg_left h1 h2
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun r _ ↦ hterm r))
  rw [← Finset.sum_div, ← Nat.cast_sum, L3Agg.hsum]
