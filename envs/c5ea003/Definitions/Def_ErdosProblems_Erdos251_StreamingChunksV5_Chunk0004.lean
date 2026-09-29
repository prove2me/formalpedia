-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0004
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0004
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:49:39.436303+00:00
-- url     : https://prove2.me/theorems/927b98b6-166b-451f-8803-13ab0daa8f51
-- title:
--   Prime-prefix checkpoint 0004
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 16384. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0004.lean#L12

import Definitions.Def_ErdosProblems_Erdos251_PrimeGapDyadicTail
import Definitions.Def_ErdosProblems_Erdos251_KernelDenominatorFloor
import Definitions.Def_ErdosProblems_Erdos251_GcdPrimality
import Definitions.Def_ErdosProblems_Erdos251_PaperStreamingCertificateV5
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0001
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0002
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0003
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

def state0004 : ℕ × ℕ := (1900, 332818170150540070246362727523623446994472335136460324760664150041796389424535445267180136738925045581525533950950609283741887758224815140405249874196549956701296029859650710045970351802627512189508482167522800260812916723684352635328088736154852793986144767229106216607238613368041993423441669243726985557201367539155521329408448918946958298835954382410638241067057018218395004486981498612446707976228780187793667586184171751657737006616844586308158651103382678482626891578772291805293009556145284223846206332578452118089661439920806054152354186928963933269700041491913923)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


