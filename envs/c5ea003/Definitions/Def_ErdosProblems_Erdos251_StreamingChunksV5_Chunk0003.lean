-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0003
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0003
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:49:00.996084+00:00
-- url     : https://prove2.me/theorems/5f8ec72a-9f83-48b3-bd73-90634a826fef
-- title:
--   Prime-prefix checkpoint 0003
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 12288. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0003.lean#L12

import Definitions.Def_ErdosProblems_Erdos251_PrimeGapDyadicTail
import Definitions.Def_ErdosProblems_Erdos251_KernelDenominatorFloor
import Definitions.Def_ErdosProblems_Erdos251_GcdPrimality
import Definitions.Def_ErdosProblems_Erdos251_PaperStreamingCertificateV5
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0001
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0002
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

def state0003 : ℕ × ℕ := (1469, 60017637668174048522662856492438349301005488546327364823219617698960074297542399639920607748139445363151451102111142587683004738619870522980382263003960093590271380106546327748835130176115173658337235030837847265112169086689972005860702448269970649535648410259960854453307520764998161042991534509820802382754488197048980296394327810464708336118075807218492351883178557082393251036797785507613566934040064442188852011134064424503274263704613055)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


