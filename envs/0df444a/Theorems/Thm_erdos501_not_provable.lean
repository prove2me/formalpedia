-- Prove2me | Theorems.Thm_erdos501_not_provable
-- name    : erdos501_not_provable
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T23:17:41.913262+00:00
-- url     : https://prove2.me/theorems/e8f9d996-1553-4bee-b727-a85ba23ea3b2
-- title:
--   Erdős 501: a negative answer is consistent with ZFC
-- statement:
--   **A negative answer to the first question of Erdős Problem 501 is consistent with ZFC.** Let $\mathrm{ZFC}$ be the Flypitch-axiomatized first-order theory of set theory (equivalent to the usual ZFC) and $\varphi_{501}$ the sentence "every complete ordered field has the Erdős property". Then
--   $$\neg\,\big(\mathrm{ZFC} \models^b \varphi_{501}\big):$$
--   not every model of $\mathrm{ZFC}$ satisfies $\varphi_{501}$ — equivalently, some model of $\mathrm{ZFC}$ satisfies its negation. By Gödel's completeness theorem, $\mathrm{ZFC}$ does not prove $\varphi_{501}$. The witness is Hechler's counterexample under CH, formalized through the Boolean-valued model of the collapse algebra $\mathrm{Col}(\omega_1, \mathcal{P}(\omega))$, where CH holds.
--
--   **Formalization Note.** $\models^b$ is Mathlib's `Theory.ModelsBoundedFormula`, quantifying over models with carrier in `Type 0`; by Löwenheim–Skolem this is no restriction.
-- source:
--   https://github.com/elliotglazer/erdos501/blob/218d1c1e46f77d4db80e566d1721782e85b94a17/Challenge.lean#L599-L604 (target 5); S. H. Hechler, Israel J. Math. 11 (1972) 231–248, https://doi.org/10.1007/BF02789314; formalized in elliotglazer/erdos501 via the collapse algebra

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Satisfiability
import Mathlib.SetTheory.ZFC.Basic
import Definitions.Def_definable_saturated_fol
import Definitions.Def_erdos501_sentence
import Definitions.Def_erdos501_zfset_structure

open MeasureTheory
open scoped Cardinal FirstOrder
open FirstOrder FirstOrder.Language
open Erdos501.FOL

universe u

theorem erdos501_not_provable : ¬ (ZFC ⊨ᵇ Erdos501) := by sorry
