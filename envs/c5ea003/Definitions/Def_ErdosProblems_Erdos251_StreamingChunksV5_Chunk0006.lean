-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0006
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0006
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:50:37.355983+00:00
-- url     : https://prove2.me/theorems/88b059e6-4141-49e5-bcea-4a149be55e38
-- title:
--   Prime-prefix checkpoint 0006
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 24576. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0006.lean#L12

import Definitions.Def_ErdosProblems_Erdos251_PrimeGapDyadicTail
import Definitions.Def_ErdosProblems_Erdos251_KernelDenominatorFloor
import Definitions.Def_ErdosProblems_Erdos251_GcdPrimality
import Definitions.Def_ErdosProblems_Erdos251_PaperStreamingCertificateV5
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0001
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0002
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0003
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0004
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0005
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

def state0006 : ℕ × ℕ := (2725, 74465215603624753019857101703390842778851818126434447796025182858920267536495696052855384097075368162128837203544953491761431296351895636916208892388441633785113497718614872340767753648563667866232332577908549300189674489806900417739362021209652200696999574504307365635915465242052791410597219553713285286841023756683725242011431476559446928999298331768953664555920533624046605826667869042075179400807291232807625080147365518127892999439651869407502082567077636653384336380201447675577379966650955280586466983056287677180605077037778335308971142395654601806575724618283257983768680741589306657234872518899198758070540364287550041660367889905559640411420174410659895207358510557978119066580845011538589703212205823992682712808134230200746724347581630927562329093023059804388069162144094137040373569915714755203288561134413)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


