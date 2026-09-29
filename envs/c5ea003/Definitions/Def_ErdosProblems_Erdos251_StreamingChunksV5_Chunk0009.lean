-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0009
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0009
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:52:40.441242+00:00
-- url     : https://prove2.me/theorems/83f46032-b4ac-4b3c-bf58-af76e431d887
-- title:
--   Prime-prefix checkpoint 0009
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 36864. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0009.lean#L12

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

def state0009 : ℕ × ℕ := (3908, 9782240181628024688332384124118652900086860751094244471161672650731493461887974592330087652329562147032380759361253469508386951668283580149357790804912625917659288918127092231057030995862925600756490341643934117837036266079531463509247292583892568315391071000528451684938064955185087864851614949432709527191554422232628677798487897318286741143904410560867808773926168295086273151168618024165410428234653841197432450394514512465531793960955449562930501366118498510387550994818493245111485726265883111001444835850517676446764043909932851027238102138317161158994927863443203311580133307467080842654025431576989043245582376584088237437359102083120021487219651838413795690034977138938982986451138157289626008180220741891777925560631327852059004200619159996705577778729388832651301930933361753782641537316415586757448807083822927016412924337570172709314434909005035680333084823167362783425303884783819726854451986737680350170148303494402563455260800851378529333730647207313187481508540454096608991650467587114596747142525133666510113384720336615750901204342589854631485154304742713958038046470697261107305831240973125841196619896631841295727412576333364892294342325536266067986243571)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


