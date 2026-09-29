-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0012
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0012
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:54:57.397974+00:00
-- url     : https://prove2.me/theorems/c4d4e008-6ed1-4f39-bc2c-d528ed049f7c
-- title:
--   Prime-prefix checkpoint 0012
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 49152. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0012.lean#L12

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

def state0012 : ℕ × ℕ := (5051, 1168754687508276025362647560751021727546001463519317522980789003160929690444017342631825574985395782494313297935318320502149016647546261854516109119073703322714440042039341613594351008951431918769453664408328214489506115370117942269605488146308709624542928532288036559377612977958479665778664085484182832310418580482342722210033516506683468454229434136271829217983919145857029610862649442506322648716906785148048205954215725552256395574293618344631015279483822953182424326458783600127198076194565410285831814491860800635451895682798402558791773930609941243328073119017376074764513406651858071665363616555844561057798008000500011949512222178981000430924944633336392004142608106676318948432699350447395691876061495788797886174443012406776647219970887357822054404033509639785227506216878312714555443337240979323144729703888210884960844323516399111694455268952246467745789527065634656669369062155425961235428901452662275141801489432634511258519795888683757996737473110588786377091546769080101741396714224789946829911958558284882870185901095092415342130306121573749739285908174238569433522393952888443321438609066465795141855579538886320871742455911864811132222895098499944080975101510023982032955714645490046288859634722988503576054295252527971938883687826565364500875359054352464256614273851750583592031546175471808741446094545666815414483531306530549567014320873906146530867899788903278033206094506206628926028260306811189138335307477286720805547072571396719891842971728025021247204446352275266467933451005229537610090073365)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


