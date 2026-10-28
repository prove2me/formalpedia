-- Prove2me | Theorems.Thm_bSet_models_infinity
-- name    : bSet_models_infinity
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T02:04:31.401214+00:00
-- url     : https://prove2.me/theorems/8866b849-8d28-4c70-bb4e-c24669d0cb33
-- title:
--   The canonical Boolean-valued omega satisfies the expanded Infinity axiom
-- statement:
--   For every nontrivial complete Boolean algebra $B$ in the designated small universe, the name universe $V^B$ gives Boolean value top to Flypitch’s expanded Infinity sentence:
--
--   $$\llbracket\mathrm{Infinity}_{\mathrm{expanded}}\rrbracket_{V^B}=1_B.$$
--
--   This sentence specifies the designated $\omega$: it contains the empty set, has no largest member, is an ordinal, and is contained in every ordinal with the first two properties. It is the least nonzero limit ordinal, as required by this axiom presentation.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Han and van Doorn, Flypitch (Apache-2.0), CPP 2020, §§2.2–5; Lean 4 port by Ian Klatzco, with Claude: https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Zfc.lean#L487-L511

import Definitions.Def_CH_Cohen_Library10
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem bSet_models_infinity : ∀ {β : Type} [inst : NontrivialCompleteBooleanAlgebra.{0} β],
  @Fol.forced_in.{1, 0} L_ZFC β (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} β inst)
    (@Top.top.{0} β
      (@BooleanAlgebra.toTop.{0} β
        (@CompleteBooleanAlgebra.toBooleanAlgebra.{0} β
          (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} β inst))))
    (@V β inst) axiom_of_infinity := by sorry
