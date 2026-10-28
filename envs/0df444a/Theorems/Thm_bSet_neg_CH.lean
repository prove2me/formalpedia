-- Prove2me | Theorems.Thm_bSet_neg_CH
-- name    : bSet.neg_CH
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T02:04:13.164377+00:00
-- url     : https://prove2.me/theorems/1ae808a5-67fc-4826-ba2e-c22c11fbb9fc
-- title:
--   The Cohen algebra forces the negation of Flypitch’s continuum hypothesis
-- statement:
--   Let $B$ be the regular-open Cohen algebra adding $\aleph_2$ binary sequences. The Boolean truth value of the negation of the native continuum hypothesis is top:
--
--   $$\llbracket\neg\mathrm{CH}_{\mathrm{native}}\rrbracket_{V^B}=1_B.$$
--
--   Here the native CH formulation forbids an uncountable ordinal $\alpha$ and a strictly larger set $y$ that injects into $\mathcal P(\omega)$. This is the Boolean-valued forcing endpoint; identifying this formulation with the mission’s membership-language sentence is a separate obligation.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Han and van Doorn, Flypitch (Apache-2.0), CPP 2020, §§2.2–5; Lean 4 port by Ian Klatzco, with Claude: https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Forcing.lean#L904-L909

import Definitions.Def_CH_Cohen_Library10
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem bSet.neg_CH : @LE.le.{0} 𝔹_cohen
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
    (@bSet.CH.{0} 𝔹_cohen 𝔹_boolean_algebra)) := by sorry
