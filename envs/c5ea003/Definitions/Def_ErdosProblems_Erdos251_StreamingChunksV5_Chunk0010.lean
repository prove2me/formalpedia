-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0010
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0010
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:53:21.139669+00:00
-- url     : https://prove2.me/theorems/3cf6fe71-f4cf-487e-9647-069f53559a1f
-- title:
--   Prime-prefix checkpoint 0010
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 40960. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0010.lean#L12

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

def state0010 : ℕ × ℕ := (4288, 24089993015695405283630410343878466624892609397393190331061651802567037162102488611103313446941782314581581525619367046800152192718011012929005069384517163793137657296289697148963996115440409124470880797736748184703256022254883938132133029104792110771012635447270003528697152850609488786923854421850497934166668657424634156310105762055385973989277864106244093455633636653454443882108211395191922280668996917616184579796687017290922870446318478429229606987281429002346659608449238234591883077396534636268460829637410502082033118518761639322721925583728581345405700603563389893124926364710071112315621157804574833696489705706267582552765424794178245687220333245339691099686836286938168229671521958313390753574587371297493397694320043112549010932168821776482556315237799184810098500260240657593820279587539126188575284604964873548970988000437980814303918301470547031505507765807502902443301490443768963182058189837072808081796511224598762194430709315383785828308458276924900562821276578965683410036067255200909268915356335528040799084449117809228453806295745619265106467530877214838528246079568839758796936817888907061967709151045549002554179226601612204389033514866723649728398353385765301899102807940771601946073787791709190886449118594104641398693722724079455582390560702348048205795370405927)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


