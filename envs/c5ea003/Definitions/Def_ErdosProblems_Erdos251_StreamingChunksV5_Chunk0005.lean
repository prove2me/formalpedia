-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0005
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0005
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:50:12.432121+00:00
-- url     : https://prove2.me/theorems/9e02afb7-2506-4ee3-9752-2911d8633ab4
-- title:
--   Prime-prefix checkpoint 0005
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 20480. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0005.lean#L12

import Definitions.Def_ErdosProblems_Erdos251_PrimeGapDyadicTail
import Definitions.Def_ErdosProblems_Erdos251_KernelDenominatorFloor
import Definitions.Def_ErdosProblems_Erdos251_GcdPrimality
import Definitions.Def_ErdosProblems_Erdos251_PaperStreamingCertificateV5
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0001
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0002
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0003
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0004
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

def state0005 : ℕ × ℕ := (2312, 3520183006397809032427228187760213687839282686591184031628179576485460220216080988035649410784134164460356506331525066964862017095400935312212595075164079330278220181988466797245249416034369441716415942350046311565204513996592146578767194142671952886280560829058105610106401251469846935237908559416713800424945194842829947447837603819437086280180388741040539935305968179808577506940298802486567609859854919026984317840192930304871305243136471272588342834502090528930414259027084296847900730839857421647028538054008625230488777117415011838882085685381642150292147677180078777107414915065006421573428408334408449888240040514713153842258416813579439278507166801243753658575836008154668834532659660477)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


