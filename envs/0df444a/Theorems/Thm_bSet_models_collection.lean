-- Prove2me | Theorems.Thm_bSet_models_collection
-- name    : bSet_models_collection
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-26T02:06:01.187654+00:00
-- url     : https://prove2.me/theorems/3e27b077-58bc-45d9-8747-6656211e4b7f
-- title:
--   Boolean-valued sets satisfy every expanded-language strong Collection instance
-- statement:
--   Let $B$ be any nontrivial complete Boolean algebra in the designated small universe, and let $\varphi(x,y,\vec p)$ be any formula of Flypitch’s expanded set-theory language, with $n$ parameters. The associated universally closed strong Collection sentence has Boolean value top in $V^B$:
--
--   $$\llbracket\forall a\,[(\forall x\in a\;\exists y\,\varphi(x,y,\vec p))\to\exists b\,((\forall x\in a\;\exists y\in b\,\varphi(x,y,\vec p))\land(\forall y\in b\;\exists x\in a\,\varphi(x,y,\vec p)))]\rrbracket=1_B.$$
--
--   The statement ranges over every bounded formula with the two displayed variables and the finite parameter tuple. It supplies the schema part of the expanded ZFC model theorem.
--
--   Original formalization: Jesse Han and Floris van Doorn. Lean 4 port: Ian Klatzco, with Claude (Apache-2.0). Adapted to the pinned Prove2Me environment.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Han and van Doorn, Flypitch (Apache-2.0), CPP 2020, §§2.2–5; Lean 4 port by Ian Klatzco, with Claude: https://github.com/ianklatzco/flypitch/blob/ad649f89e9f3107b7e2ea97a58b2eafdfc80b815/flypitch4/Flypitch4/Zfc.lean#L395-L423

import Definitions.Def_CH_Cohen_Library10
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem bSet_models_collection : ∀ {β : Type} [inst : NontrivialCompleteBooleanAlgebra.{0} β] {n : Nat}
  (ϕ :
    Fol.bounded_formula.{1} L_ZFC
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))),
  @Fol.forced_in.{1, 0} L_ZFC β (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} β inst)
    (@Top.top.{0} β
      (@BooleanAlgebra.toTop.{0} β
        (@CompleteBooleanAlgebra.toBooleanAlgebra.{0} β
          (@NontrivialCompleteBooleanAlgebra.toCompleteBooleanAlgebra.{0} β inst))))
    (@V β inst) (@axiom_of_collection n ϕ) := by sorry
