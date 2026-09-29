-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0014
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0014
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:57:03.762292+00:00
-- url     : https://prove2.me/theorems/d55f1964-0f38-4541-ba83-949e69d45696
-- title:
--   Prime-prefix checkpoint 0014
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 57344. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0014.lean#L12

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

def state0014 : ℕ × ℕ := (5814, 56703524931808122082386036307550001991759150255797266073727473836133449718917142151519276012452128466301586845735756500034704246909612111103601872625520818610790282294726707553632899919366864777489147519588357331093555454989443362390151793421460621843221767755715861362092503338331481448464528066950303835021216873367268512176540005189212617655001838726167884628282765004747997135321952566289312368096522469481899387184568104907629144496261198157415431616086525815131434893420109703422886405509871998751760515675281812180302493695725307664551406945261367870868599797339350230802900592451210683713224277948675388585964888118909981460118528889261678379629519964361837474518635820895813463817522492856296404971796491367729668148670773375589505607115937903729400227978392893836810727451033261800298487123711338378197119481139780184234381022850461649635295583223634406398995255145659218360234728979564814804712238253365554989098084461977422781116223128620827502121170613131784018232577422596722430117163632724073946088081156048853393026568680181056512882316746908137902397849205092996037747140711087538621172762713051611835527318735336407855988267714500682491750809362585518057679726437229991977692805771563701719272722878700000867426813518687229194511344677244392340943125459898260114104850877306958041276183858664006395348019176144464437901233738733648059322352025026240164091939440265038685843648046390016012103233449702809929567088283988947733554169202369396808812813907473010116039573850016745147333275654493140813906235894395914962216941306266433336073743413575856961133044554031375277207614189887478285784177316850285546529081835800303690574276711103272639354460770937931261261147947494158187918053173741708808008967728700846214052443525200030104625)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


