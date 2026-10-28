-- Prove2me | Theorems.Thm_bSet_models_ZFC
-- name    : bSet_models_ZFC
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T02:06:53.752998+00:00
-- url     : https://prove2.me/theorems/2b2a2fa1-0988-415d-9bf7-b84b5e4ae341
-- title:
--   The Boolean-valued name universe models Flypitch’s expanded ZFC theory
-- statement:
--   Let $B$ be any nontrivial complete Boolean algebra in the designated small universe. The Boolean-valued name universe satisfies every sentence of Flypitch’s expanded ZFC presentation:
--
--   $$\forall\sigma\in T_{\mathrm{expanded}},\quad\llbracket\sigma\rrbracket_{V^B}=1_B.$$
--
--   The expanded language has membership and five function symbols. Its finite axioms specify the empty set, ordered pairing, extensionality, union, power set, the designated $\omega$, regularity, and Zorn’s lemma; its schema is strong Collection. This theorem concerns that exact native presentation. Its transfer to the mission’s membership-only ZFC theory is stated separately.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Han and van Doorn, Flypitch (Apache-2.0), CPP 2020, §§2.2–5; Lean 4 port by Ian Klatzco, with Claude: https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Zfc.lean#L569-L585

import Definitions.Def_CH_Cohen_Library10
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem bSet_models_ZFC : ∀ {β : Type} [inst : NontrivialCompleteBooleanAlgebra.{0} β],
  @Fol.all_forced_in.{1, 0} L_ZFC β (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} β inst)
    (@Top.top.{0} β
      (@BooleanAlgebra.toTop.{0} β
        (@CompleteBooleanAlgebra.toBooleanAlgebra.{0} β
          (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} β inst))))
    (@V β inst) ZFC := by sorry
