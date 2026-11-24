-- Prove2me | Theorems.Thm_erdos501_independent
-- name    : erdos501_independent
-- status  : Open
-- author  : @LG
-- created : 2026-11-23T23:18:02.091804+00:00
-- url     : https://prove2.me/theorems/6b2f07fc-8e99-470a-ac7c-a141cfccd1ce
-- title:
--   Erdős 501, first question: independence from ZFC
-- statement:
--   **The first question of Erdős Problem 501 is independent of ZFC**: neither $\varphi_{501}$ nor its negation is a consequence of $\mathrm{ZFC}$:
--   $$\neg\,\big(\mathrm{ZFC} \models^b \varphi_{501}\big)\ \wedge\ \neg\,\big(\mathrm{ZFC} \models^b {\sim}\varphi_{501}\big).$$
--   Here $\mathrm{ZFC}$ is the Flypitch-axiomatized first-order theory of set theory (equivalent to the usual ZFC) and $\varphi_{501}$ is the sentence "every complete ordered field has the Erdős property" — the first-order rendering of: for every family $(A_x)_{x \in \mathbb{R}}$ of bounded sets of outer measure $< 1$ there is an infinite independent set. The two conjuncts are Target 4 (Glazer–Sol 2026: a positive answer holds after adding $\mathfrak{c}^+$ random reals) and Target 5 (Hechler 1972: a negative answer holds in the collapse extension, where CH holds). By Gödel's completeness theorem, neither answer is provable from ZFC; neither adds consistency strength. This is the mission's goal theorem.
--
--   **Formalization Note.** $\models^b$ is Mathlib's `Theory.ModelsBoundedFormula` over models with carrier in `Type 0` (no restriction, by Löwenheim–Skolem); $\sim$ is bounded-formula negation.
-- source:
--   https://github.com/elliotglazer/erdos501/blob/218d1c1e46f77d4db80e566d1721782e85b94a17/Challenge.lean#L606-L609 (target 6); E. Glazer, Sol (2026), https://github.com/elliotglazer/erdos501/blob/main/docs/paper/erdos501_random_profiles_rev10.pdf; S. H. Hechler (1972), https://doi.org/10.1007/BF02789314

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

theorem erdos501_independent : ¬ (ZFC ⊨ᵇ Erdos501) ∧ ¬ (ZFC ⊨ᵇ ∼Erdos501) := by sorry
