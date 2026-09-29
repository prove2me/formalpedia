-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_StreamingChunksV5_Chunk0013
-- name    : ErdosProblems_Erdos251_StreamingChunksV5_Chunk0013
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T20:55:55.478213+00:00
-- url     : https://prove2.me/theorems/a1ad9b70-af24-452a-b8be-17108e7e6de4
-- title:
--   Prime-prefix checkpoint 0013
-- statement:
--   Defines the exact prime-count and binary Horner-accumulator pair after scanning integers below 53248. The paired block and endpoint theorems independently check this explicit checkpoint in Lean.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/6e2d392bd294bd9883859fb86c49655e7567086e/ErdosProblems/Erdos251/StreamingChunksV5/Chunk0013.lean#L12

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

def state0013 : ℕ × ℕ := (5432, 5756409929908273147636624091335652643364949945829343860057624334962248350204431229218715286960575085549566288606689185305371908979315831512422219593602717090358985661105471085424564547631878918361849218104220897366059420411724499202835886009052415240627188850162233806592590741163244967155847859612044318179668879539342237211382922053865192213321672998996024550673000900914753090928753465963077244924457136155513385269221373367356293590559619357628271984239786522755520825100306722303593161799635032249745980100167424053210672809881774369922375658092886051461785455151866103486613745941180097054179414919839148038712637639416424467401232528585392084715909173222207920476147126412747022301866901982262401761955118038544204645168201093378026028596487386559533040088489431550149275798495436057553376178615641300335152759438604798242936089500583608439482439010351765840949695672865855063366689071651206751693592665797798070748983044794654062454512957054593692223928204926202509269403150480665595530394093255664793187310244857073280028931322145520274885029294087796604009751870449277482668134808788318182787511229486104432904309306747158521222592353715055674241185094503201096025210891502109679484326003415080024689108735575608634296729624862125282947152379630672104791729180773959079491955273764480171181115699853456810038094544094957763294946531326639633780611025267568326442935666136891344986567982258397194685732838796329965351062008133238192518556194342615553681396081503751172171340171792930454283023435367393896531615153603577311963803354059018526505216674288214309109353353748896705723147613136447909511127054285311010930365484773709)





end ErdosProblems.Erdos251.PaperV5.Streaming.Chunks


