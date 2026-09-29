-- Prove2me | solution 1 for mme_released_recursive_stage_region0_coarse_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T04:56:10.240118+00:00
-- url     : https://prove2.me/submissions/74b2a0ec-dbbf-4ba5-a098-711de03f3b42

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
import Theorems.Thm_mme_released_recursive_stage_region0_counts
import Theorems.Thm_mme_released_recursive_level3_coarse0
import Theorems.Thm_mme_released_recursive_level3_coarse1
import Theorems.Thm_mme_released_recursive_level3_coarse2
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.RegionRate
  MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace L3Agg

/-- The certified floor numerator of each region, over the common denominator `10^30`. -/
def cfn (r : Fin 88) : ℕ := if r.val = 0 then 693147180557621093303788000000 else if r.val = 1 then 693147180559944616464256000000 else if r.val = 2 then 693147180559931020083788000000 else if r.val = 3 then 693147180559903681992448000000 else if r.val = 4 then 693147120551243230191973300339 else if r.val = 5 then 900555786198873215380917355445 else if r.val = 6 then 911275493466533215811846277514 else if r.val = 7 then 904148507341222758435583014108 else if r.val = 8 then 908333282906631431659016136114 else if r.val = 9 then 809626625429746788228623425964 else if r.val = 10 then 812612010370956283422246643728 else if r.val = 11 then 809368863690079037868063431970 else if r.val = 12 then 811731266303261404836863156328 else if r.val = 13 then 555854756950930254444435106629 else if r.val = 14 then 769479411425482186167721897559 else if r.val = 15 then 711976104258674641619546421463 else if r.val = 16 then 693147180559619816346832000000 else if r.val = 17 then 693147180559945134913132000000 else if r.val = 18 then 693147180559939087993856000000 else if r.val = 19 then 693146883226389673391137512447 else if r.val = 20 then 908848576901332390516255259746 else if r.val = 21 then 911395109752143863924554664810 else if r.val = 22 then 904134294053043176435190090736 else if r.val = 23 then 900143281684103741935297179379 else if r.val = 24 then 812706612645017064015083489772 else if r.val = 25 then 812619737579763544362967928339 else if r.val = 26 then 809265226404075963387786724975 else if r.val = 27 then 810272817366879618724364025342 else if r.val = 28 then 555854434454634159370925652310 else if r.val = 29 then 769467640694981510114992996746 else if r.val = 30 then 711896058627967083758254535474 else if r.val = 31 then 693147180559650970616332000000 else if r.val = 32 then 693147180559945306520428000000 else if r.val = 33 then 693147180559939773759628000000 else if r.val = 34 then 693147180559932520521488000000 else if r.val = 35 then 693147180373815825004048000000 else if r.val = 36 then 900628665580315766929266797713 else if r.val = 37 then 911349132061385003361554116252 else if r.val = 38 then 904427131354296295448399588481 else if r.val = 39 then 911281491506505390544343957706 else if r.val = 40 then 809118194603984395335597695869 else if r.val = 41 then 811794464518464740581171904405 else if r.val = 42 then 808694830491075194687653057301 else if r.val = 43 then 812093434539130765117514227374 else if r.val = 44 then 541183994604786622867358920394 else if r.val = 45 then 768129296695063727359260047081 else if r.val = 46 then 705546273754807564419467084968 else if r.val = 47 then 693147180538304503144208000000 else if r.val = 48 then 693147180559943596119568000000 else if r.val = 49 then 693147180559944229111808000000 else if r.val = 50 then 693147180559932184965388000000 else if r.val = 51 then 693147180381900640434988000000 else if r.val = 52 then 909018675962937370541545888299 else if r.val = 53 then 911572080208014257678585547337 else if r.val = 54 then 904545515529794066092388100715 else if r.val = 55 then 911390881298084554412658570906 else if r.val = 56 then 811863572810883420035569230041 else if r.val = 57 then 811300120261335144305300179639 else if r.val = 58 then 808205215023607930219899573387 else if r.val = 59 then 811593908518543004741843400323 else if r.val = 60 then 695811142749872007098311112911 else if r.val = 61 then 693147171639299387253617349348 else if r.val = 62 then 693147180559945250526956000000 else if r.val = 63 then 693147180559942589794732000000 else if r.val = 64 then 693146883612921187278877001735 else if r.val = 65 then 913526591817096872941452372116 else if r.val = 66 then 904124171690608764942498365949 else if r.val = 67 then 900212286091271437980552632743 else if r.val = 68 then 814020997571556262646186274152 else if r.val = 69 then 811872885977731439162263465055 else if r.val = 70 then 808499677986548161859566118168 else if r.val = 71 then 809558546240310416130717287693 else if r.val = 72 then 541190163305253896507708744179 else if r.val = 73 then 768130699273850125863518832468 else if r.val = 74 then 705541177832590360516657868146 else if r.val = 75 then 693147171639624124828193384455 else if r.val = 76 then 693147180559945244775632000000 else if r.val = 77 then 693147180559943702690176000000 else if r.val = 78 then 693147180559932815543056000000 else if r.val = 79 then 693147120625953775262846680456 else if r.val = 80 then 913647122748691780373737902752 else if r.val = 81 then 904446127607146579504889154834 else if r.val = 82 then 908483299955031022045957411993 else if r.val = 83 then 813659824156934954085343402929 else if r.val = 84 then 811366612583904607901922748229 else if r.val = 85 then 808097864634233751147904727478 else if r.val = 86 then 810507477908675725362008831130 else if r.val = 87 then 695750848578236785320619975040 else 0

/-- A single region's certificate, turned into a bound on its entropy. -/
theorem cstep {r : Fin 88} {e : Fin 5 → Fin 4 → ℤ} {q : ℚ}
    (h : q ≤ regFloorG (normQ (marginalCounts (m3 0) 0 r)) e) :
    ((q : ℚ) : ℝ) ≤
      entropy (fun j ↦ ((normQ (marginalCounts (m3 0) 0 r) j : ℚ) : ℝ)) :=
  le_trans (by exact_mod_cast h)
    (mme_certified_entropy_rational_floor.1 (normQ (marginalCounts (m3 0) 0 r))
      (fun j ↦ mme_certified_entropy_bridge.{0, 0}.2.2.2.2.1 (marginalCounts (m3 0) 0 r) j)
      e _ _ rfl (fun _ ↦ rfl))

theorem hent : ∀ r : Fin 88,
    ((cfn r : ℕ) : ℝ)/10^30 ≤
      entropy (fun j ↦ ((normQ (marginalCounts (m3 0) 0 r) j : ℚ) : ℝ)) := by
  intro r
  match r with
  | ⟨0, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.1
  | ⟨1, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.1
  | ⟨2, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.1
  | ⟨3, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.1
  | ⟨4, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.1
  | ⟨5, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.1
  | ⟨6, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.1
  | ⟨7, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.1
  | ⟨8, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.1
  | ⟨9, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.1
  | ⟨10, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.1
  | ⟨11, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨12, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨13, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨14, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨15, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨16, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨17, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨18, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨19, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨20, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨21, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨22, _⟩ => simpa using cstep mme_released_recursive_level3_coarse0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | ⟨23, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.1
  | ⟨24, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.1
  | ⟨25, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.1
  | ⟨26, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.1
  | ⟨27, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.1
  | ⟨28, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.1
  | ⟨29, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.1
  | ⟨30, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.1
  | ⟨31, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.1
  | ⟨32, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.1
  | ⟨33, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.1
  | ⟨34, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨35, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨36, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨37, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨38, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨39, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨40, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨41, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨42, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨43, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨44, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨45, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨46, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨47, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨48, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨49, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨50, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨51, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨52, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨53, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨54, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨55, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨56, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨57, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨58, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨59, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨60, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨61, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨62, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨63, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨64, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨65, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨66, _⟩ => simpa using cstep mme_released_recursive_level3_coarse1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | ⟨67, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.1
  | ⟨68, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.1
  | ⟨69, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.1
  | ⟨70, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.1
  | ⟨71, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.1
  | ⟨72, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.1
  | ⟨73, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.1
  | ⟨74, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.1
  | ⟨75, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.1
  | ⟨76, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.2.1
  | ⟨77, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨78, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨79, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨80, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨81, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨82, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨83, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨84, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨85, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨86, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | ⟨87, _⟩ => simpa using cstep mme_released_recursive_level3_coarse2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | ⟨n + 88, h⟩ => exact absurd h (by omega)

/-- The weighted total, as one natural number. -/
theorem hsum : ∑ r : Fin 88, n3 0 r * cfn r = 735852980828408872615626123927860111521137282486281063000000000000000000000000000000000000 := by decide +kernel

end L3Agg

theorem solution :
    ((735852980828408872615626123927860111521137282486281063000000000000000000000000000000000000 : ℕ) : ℝ)/10^30 ≤ coarsePotential (m3 0) 0 := by
  have hc := mme_released_recursive_stage_region0_counts
  have hpos : ∀ r, 0 < ∑ j, marginalCounts (m3 0) 0 r j := by
    intro r
    rw [mme_certified_rate_entry.{0}.1 (m3 0) 0 r, hc.2 r]
    exact hc.1 r
  have hw : ∀ r, (∑ j, marginalCounts (m3 0) 0 r j) = n3 0 r := by
    intro r
    rw [mme_certified_rate_entry.{0}.1 (m3 0) 0 r, hc.2 r]
  rw [mme_certified_entropy_bridge.{0, 0}.2.2.2.2.2 (m3 0) 0 hpos]
  have hterm : ∀ r : Fin 88,
      ((n3 0 r * L3Agg.cfn r : ℕ) : ℝ)/10^30 ≤
        ((∑ j, marginalCounts (m3 0) 0 r j : ℕ) : ℝ) *
          entropy (fun j ↦ ((normQ (marginalCounts (m3 0) 0 r) j : ℚ) : ℝ)) := by
    intro r
    rw [hw r]
    have h1 := L3Agg.hent r
    have h2 : (0 : ℝ) ≤ ((n3 0 r : ℕ) : ℝ) := by positivity
    calc ((n3 0 r * L3Agg.cfn r : ℕ) : ℝ)/10^30
        = ((n3 0 r : ℕ) : ℝ) * (((L3Agg.cfn r : ℕ) : ℝ)/10^30) := by push_cast; ring
      _ ≤ ((n3 0 r : ℕ) : ℝ) * entropy _ := mul_le_mul_of_nonneg_left h1 h2
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun r _ ↦ hterm r))
  rw [← Finset.sum_div, ← Nat.cast_sum, L3Agg.hsum]
