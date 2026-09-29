-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0015
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0015
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:57:39.777161+00:00
-- url     : https://prove2.me/theorems/eb938c14-fbca-458d-b853-994a33922f97
-- title:
--   Prime-prefix checkpoint 0015
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 61440. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0015.lean#L12

import Definitions.Def_ErdosProblems_Erdos251_PrimeGapDyadicTail
import Definitions.Def_ErdosProblems_Erdos251_KernelDenominatorFloor
import Definitions.Def_ErdosProblems_Erdos251_GcdPrimality
import Definitions.Def_ErdosProblems_Erdos251_PaperStreamingCertificateV5
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0001
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0002
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0003
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0004
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0005
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0006
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0007
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0008
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0009
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0010
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0011
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0012
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0013
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0014
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PowModTotient
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

                                                               
                                                                    
                                                  
namespace ErdosProblems.Erdos251.PaperV5.Streaming.Chunks
open ErdosProblems.Erdos251.PaperV5.Streaming
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option exponentiation.threshold 200000

def state0015 : ℕ × ℕ := (6179, 4261460572663330966228186805846582838602226503787663372960465456250787587014661108629987246209399523408236036466511228008836059591247346775599903669300780169745321614305554482181004194828618423947993902582874997568382400831619789944578993489070413497512731343909613401000005062843994037403919669223424208710951492089432120607207272789877908883719831861716610103667929511195821400953308529843244527985481835701052177468470876009028801337628165376931216791548801238654765347327228193402775842730961600640025676834006483632238404215452028318588482162220557472696395229993437402688554697116442774391952299266409630227460342102711688447490328454703622699642308470140692919895887375670861044216620867657985223651396958159591677695468337859443223215663789091368807919301110448798919508746540001514359388693350748941570463339893213740164765864355408676023819628884765940625409502425834090466092206236507665962200020231021059971940347504072632403553145382004820621970287802356458689065169285911232324426004867111838644303032628193676031724637555496581167116586661778424079903097962685858906821014730746534973915550447934367321873563554250276379978413694157388150438223349916675924400002937471967550698040957995170290033155445691346929093674596728543874157196156005101603497062169199814969641276701258408345185788680763204679271404113850336739580008880306853135943157212560771373556341251300202615397023374675602074296226796893747084351973365106489664175170904497137630056823235451330023657701664859982031411575897643050599199880690651806129133623410184266407302777917338587398128558745265037165662292869526014965811235545463654808231993079062824098220724954128584776994471911159744090388241360007187721214196764999207754179010132695565426698321180334842256274870188459360090054332712368875221659159055140901424738212873505005670034352998209559991706361015289558365971343)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


