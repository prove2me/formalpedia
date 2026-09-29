-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0016
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0016
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:58:16.523549+00:00
-- url     : https://prove2.me/theorems/7277561c-64d5-459f-b74d-9a77140bec86
-- title:
--   Prime-prefix checkpoint 0016
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 65536. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0016.lean#L12

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
import Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0015
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

def state0016 : ℕ × ℕ := (6542, 80065772957692781716911364173707693806923975583572085017654928359338571079543800919362424666970439125466506139503243008137283389711660472707419204601391473859983182347148128847175829286515473914886362561205180008235634906580537503565130009423723718867680601061975445727026571741759619540053514235872744684664976454169093015421172523420706884027259443259714782961847504475412977416965337817209329572219305429755277039838781066310815359839801090048195253305410878135876216567982564672298307843324974458530955116476400078044241385844059344296014898326495601511647869017501309916398154992924622566829269642425887680731088309627676838354964902142973495946209851770294562659009426351727616982257087813516803954994623342542684298003922438041779351361984344729744780424225583146419590409529120546831378001649976365840223472040062584775511719198261035365708724015037305226663144473254177137160081535828866647304798404175421382170639568048919875080105717087348950675447141227596084571202298154609552535286744038973035450145449782992839862800050562882415467113116986748737295017032038433487942317941751913391965428559189560724569320178679175576427528610555667676613211309613157960538209576347505146213007500906509478765255361360975280144175482558806563290633507416377277722510218029074504915060475075042446479322204969125543770575665955573480282342787490585166803197026898321681329321382626097722822065418370161289096785260778942196236892642835148287828013699311574209865115451264518478720000208843085735944936228527554685433573745326612644412023167632471147077532735359948865316329322839423866458495666762453776849947452326157926592831954407699528732331437332727869299045253194754637023113265021101397517986238910866960407031405776572885493281952517983357070574600210213805340832902729316828980951176604190578633342453203116343781277296105616388402188575956062872088484025962129658969072820320496144378949969329203715731497710864525585598042727331998270635746375135382046830044315)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


