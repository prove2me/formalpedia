-- Prove2me | Theorems.Thm_bSet_aleph1_lt_aleph2_bSet
-- name    : bSet.aleph1_lt_aleph2_bSet
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T02:06:54.926851+00:00
-- url     : https://prove2.me/theorems/28bd555b-ec94-4ef4-a1fc-f68afee0a125
-- title:
--   Cohen forcing preserves the gap between the first two uncountable ground-model cardinals
-- statement:
--   Let $B$ be the regular-open Cohen algebra adding $\aleph_2$ binary sequences. In its Boolean-valued universe there is no surjection from any subset of the canonical ground-model $\aleph_1$ onto the canonical ground-model $\aleph_2$:
--
--   $$\llbracket\neg\exists d\subseteq\check{\aleph_1}\;\exists f:d\twoheadrightarrow\check{\aleph_2}\rrbracket=1_B.$$
--
--   This keeps the larger family of Cohen reals strictly above the ordinal used as the uncountable witness.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Han and van Doorn, Flypitch (Apache-2.0), CPP 2020, §§2.2–5; Lean 4 port by Ian Klatzco, with Claude: https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Forcing.lean#L823-L827

import Definitions.Def_CH_Cohen_Library10
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem bSet.aleph1_lt_aleph2_bSet : @LE.le.{0} 𝔹_cohen
  (@Preorder.toLE.{0} 𝔹_cohen
    (@PartialOrder.toPreorder.{0} 𝔹_cohen
      (@ChainCompletePartialOrder.toPartialOrder.{0} 𝔹_cohen
        (@ChainCompletePartialOrder.instOfCompleteLattice.{0} 𝔹_cohen
          (@CompleteBooleanAlgebra.toCompleteLattice.{0} 𝔹_cohen
            (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} 𝔹_cohen 𝔹_boolean_algebra))))))
  (@Top.top.{0} 𝔹_cohen
    (@BooleanAlgebra.toTop.{0} 𝔹_cohen
      (@CompleteBooleanAlgebra.toBooleanAlgebra.{0} 𝔹_cohen
        (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} 𝔹_cohen 𝔹_boolean_algebra))))
  (@Compl.compl.{0} 𝔹_cohen
    (@BooleanAlgebra.toCompl.{0} 𝔹_cohen
      (@CompleteBooleanAlgebra.toBooleanAlgebra.{0} 𝔹_cohen
        (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} 𝔹_cohen 𝔹_boolean_algebra)))
    (@bSet.larger_than.{0} 𝔹_cohen 𝔹_boolean_algebra
      (@bSet.check.{0} 𝔹_cohen 𝔹_boolean_algebra
        (PSet.card_ex.{0}
          (@DFunLike.coe.{2, 2, 2}
            (@OrderEmbedding.{1, 1} Ordinal.{0} Cardinal.{0}
              (@Preorder.toLE.{1} Ordinal.{0} (@PartialOrder.toPreorder.{1} Ordinal.{0} Ordinal.partialOrder.{0}))
              Cardinal.instLE.{0})
            Ordinal.{0} (fun x => Cardinal.{0})
            (@instFunLikeOrderEmbedding.{1, 1} Ordinal.{0} Cardinal.{0}
              (@Preorder.toLE.{1} Ordinal.{0} (@PartialOrder.toPreorder.{1} Ordinal.{0} Ordinal.partialOrder.{0}))
              Cardinal.instLE.{0})
            Cardinal.aleph.{0}
            (@OfNat.ofNat.{1} Ordinal.{0} (nat_lit 1) (@One.toOfNat1.{1} Ordinal.{0} Ordinal.one.{0})))))
      (@bSet.check.{0} 𝔹_cohen 𝔹_boolean_algebra
        (PSet.card_ex.{0}
          (@DFunLike.coe.{2, 2, 2}
            (@OrderEmbedding.{1, 1} Ordinal.{0} Cardinal.{0}
              (@Preorder.toLE.{1} Ordinal.{0} (@PartialOrder.toPreorder.{1} Ordinal.{0} Ordinal.partialOrder.{0}))
              Cardinal.instLE.{0})
            Ordinal.{0} (fun x => Cardinal.{0})
            (@instFunLikeOrderEmbedding.{1, 1} Ordinal.{0} Cardinal.{0}
              (@Preorder.toLE.{1} Ordinal.{0} (@PartialOrder.toPreorder.{1} Ordinal.{0} Ordinal.partialOrder.{0}))
              Cardinal.instLE.{0})
            Cardinal.aleph.{0}
            (@OfNat.ofNat.{1} Ordinal.{0} (nat_lit 2)
              (@instOfNatAtLeastTwo.{1} Ordinal.{0} (nat_lit 2)
                (@AddMonoidWithOne.toNatCast.{1} Ordinal.{0} Ordinal.addMonoidWithOne.{0})
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))))) := by sorry
