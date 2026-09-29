-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0007
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0007
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:51:00.258326+00:00
-- url     : https://prove2.me/theorems/957628a4-6440-4332-b9a6-4f8e8b525a58
-- title:
--   Prime-prefix checkpoint 0007
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 28672. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0007.lean#L12

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

def state0007 : ℕ × ℕ := (3124, 96143896957087690854920552791599586856750108677135698578852712089938757612436664979722871941709912086574339972446571662882315016731762123757766942484416921965045329910361392036272438924237368939317762066123997068945968245037089696945415375484756432017270965336105870464832819059290224558508591555467650050269360137401725638730093899726191562564763697997385969779791814691987329013417954667856203702730035203330711989636715012572821146153586248221678643002922691502850581401907708489458746181981246303322740738606544332117546562723781708691008090794588640126800836088248506147590065634459726876050789720332542857620245225139769862471657754898317365214635791717145503035824857490605078965908875852184413525033790243486523137308317147352601244511047293185567261693964425471215345729165502374016657221978718262231284958469548005170788605698044399221901612971342370354034846852274502071892838916206873602864670336121811350290136708084113325232247)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


