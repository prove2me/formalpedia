-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0008
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0008
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:51:43.515452+00:00
-- url     : https://prove2.me/theorems/00bbac0c-398e-4426-9afc-3a5065df6200
-- title:
--   Prime-prefix checkpoint 0008
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 32768. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0008.lean#L12

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

def state0008 : ℕ × ℕ := (3512, 60612198778378904158687700974732859518570726360182013126418921691239446440360528226329112538768828798309972127665378993867214717881796361941895567548419525274251007993864410853609931907916002560829811672042285575070768639407830935614417329991618748258860016349411545927441213142618710786860379080887715511409100826352152374593999183535974991576532002763221949653146087255352634832401472962361780506673454005976250924434482116960900597221380102422853518450247624085471549683322167541854579056616792267326967482515983828112032194187584114003463669963634644371827195141524503533272263586587556757808292097207307095892833790854895927888354260585663400320141693729388001539519217707874962997538453137351316652735374961684713309070999585446346385060267818748280611037923123677866585533892627332769730614337488478944076314141373125776767742632580592652970690270460215775026077722433253505988925025332484571307885305772397035912378488641142202820215626105360798485009834787887902455611025398511258409956887952609185671510603028639248567677611499620995168274741139223)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


